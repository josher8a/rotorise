/**
 * **The pool of the entry methods: the type against the run time.**
 *
 * A draw is an entity typing, a key schema with its options, and the calls of the methods of an entry.
 * The run time is the oracle of each row. The spec runs each call with no type, and prints one line
 * for the type checker for each decision. The gate compiles the lines and holds the disagreements
 * to a list, as it does for the codecs: `formal/scripts/type_bridge.py` reads `formal/.entry.types/`.
 *
 *   construct  The row is an `accept` row where the construction builds, and `toEntry` builds each
 *              plain item of the draw. A plain item is an item that the declared type alone fixes: each
 *              leaf is a text of one character or more with no separator, a number or a boolean. The
 *              row is a `refuse` row where the construction throws, or where `toEntry` throws for a
 *              plain item. A throw for another item moves no construct row: the host cannot state
 *              the empty text or a text with the separator. A refuse row prints no method row.
 *   call       The call of a method, with the argument as a variable of the declared type, so no excess
 *              property check gives the verdict. An `accept` row where the run time gives a value.
 *   result     The value of the run time, assigned to the type of the result. An `accept` row.
 *   foreign    One value that the run time cannot give at that call, under `@ts-expect-error`. A key
 *              text with a label (`PETID#p1`): the text with `~` in front. A key that the run time does
 *              not write: the key with the text `~#~`, for a spec whose arm for the member is `null`.
 *              A text with no label has no foreign value, and an attribute key can hold any text.
 *              `infer` has no foreign row for a spec with an attribute or a path, because another member
 *              of the union can hold any text there. fromEntry: the item with the first key name.
 *              keyUpdates: the patch with `remove: ['~']`.
 *   typing     An item of the draw, assigned to the entity type. An error here is a defect of the
 *              generator, and the bridge fails it as a hard failure.
 *
 * A `refuse` row can state `at`, the text where its first error must start, and `rule`, a text that a
 * library rule message must hold. A call row states its argument variable. A foreign property row states
 * the property. The negative pole of a kind states the name that the entity lacks, and the rule of the
 * library for that name. A foreign result of `key` states no site: the compiler puts the error of
 * `const r: T = "text"` on the declared name, so the site would test the row and not the type. The bridge
 * reads `at` and `rule` as the ids `site|<id>` and `text|<id>`.
 *
 * A row that reads the result of another row names that row in `after`. The bridge gives no verdict
 * at a row whose `after` row disagrees, or is a `refuse` row. The id of a row is the group, the
 * verdict of the run time, a hash of the draw, and the text of the check. The hash of a typing row
 * is the hash of the entity, so no id depends on the order of the draws.
 */
import { createHash } from 'node:crypto'
import { mkdirSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import ts from 'typescript'
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../Rotorise'
import {
    CodecError,
    discriminatedUnion,
    held,
    item,
    nullable,
    number,
    object,
    optional,
    string,
    union,
} from '../codec'

// ---------------------------------------------------------------- the text and the run

const PRELUDE: readonly (readonly [string, string])[] = [
    [
        'schemaOf',
        '<T>(is: (v: unknown) => v is T): StandardSchemaV1<T> => ({ "~standard": { version: 1, vendor: "test", validate: (v) => (is(v) ? { value: v } : { issues: [{ message: "no" }] }) } })',
    ],
    [
        'Adopted',
        "held(string('Y', 'N'), schemaOf((v): v is boolean => typeof v === 'boolean'), { encode: (b: boolean) => (b ? 'Y' : 'N'), decode: (s: string) => s === 'Y' })",
    ],
    [
        'TaggedPets',
        "item(discriminatedUnion('species', [object({ petId: string, species: string('CAT'), status: string('IN', 'OUT'), adopted: Adopted }), object({ petId: string, species: string('DOG'), status: string('IN'), adopted: Adopted })]))",
    ],
    [
        'UntaggedPets',
        "item(union([object({ petId: string, species: string('CAT'), adopted: Adopted }), object({ petId: string, species: string('DOG'), adopted: Adopted })]))",
    ],
]
const LIBRARY = {
    tableEntry,
    discriminatedUnion,
    held,
    item,
    nullable,
    number,
    object,
    optional,
    string,
    union,
}
const evaluate = (text: string, scope: Record<string, unknown>): unknown => {
    const code = ts.transpileModule(`export default (${text})`, {
        compilerOptions: {
            module: ts.ModuleKind.CommonJS,
            target: ts.ScriptTarget.ES2022,
        },
    }).outputText
    const names = Object.keys(scope)
    const exported: { default?: unknown } = {}
    new Function('exports', ...names, code)(
        exported,
        ...names.map((n) => scope[n]),
    )
    return exported.default
}
const SCOPE: Record<string, unknown> = { ...LIBRARY, anyDepth: undefined }
for (const [name, text] of PRELUDE) SCOPE[name] = evaluate(text, SCOPE)
const ev = (text: string): unknown => evaluate(text, SCOPE)

type Outcome =
    | { readonly ok: true; readonly value: unknown }
    | { readonly ok: false; readonly message: string }
const attempt = (f: () => unknown): Outcome => {
    try {
        return { ok: true, value: f() }
    } catch (cause) {
        const message = cause instanceof Error ? cause.message : String(cause)
        return {
            ok: false,
            message: message.replace(/\s+/g, ' ').slice(0, 150),
        }
    }
}
const lit = (value: unknown): string => {
    if (value === undefined) return 'undefined'
    if (value === null || typeof value !== 'object')
        return JSON.stringify(value)
    if (Array.isArray(value)) return `[${value.map(lit).join(', ')}]`
    return `{ ${Object.entries(value)
        .filter(([, v]) => v !== undefined)
        .map(([k, v]) => `${JSON.stringify(k)}: ${lit(v)}`)
        .join(', ')} }`
}

// ---------------------------------------------------------------- the catalog

type Var = {
    readonly declared: string // `$E` is the entity type
    readonly value: string
    readonly vk: string // the axis "value": what the value does to a carrier
    readonly wide?: boolean // the value holds a member that the declared type lacks
}
type Config = {
    readonly text: string
    readonly run: string
    readonly pre?: readonly string[]
}
type Spec = {
    readonly id: string
    readonly form: string // the axis "form": the shape of the key spec
    readonly codec: string // the axis "codec": none, record, tagged, held
    readonly schema: string
    readonly options?: string | undefined
    readonly keys?: readonly string[]
    readonly keyArgs?: readonly string[]
    readonly configs?: readonly string[]
    readonly items?: readonly string[] // the items of toEntry, fromEntry and infer
    readonly changes?: readonly string[]
    readonly calls?: readonly string[] // the methods that have no other loop: keys, keyCondition, toItem, fromItem, encodePartial
    readonly args?: readonly string[] // the arguments of keys and keyCondition: Partial<Entity>, so a prefix or none is drawn
    readonly patches?: readonly string[] // the changes that encodePartial reads
    readonly at?: string // construct: the text of the element where the error must start
    readonly rule?: string // construct: a text that the library rule message must hold
    readonly indexes?: readonly string[] // the names of the indexes that keyCondition reads
    readonly extra?: Readonly<Record<string, string>> // more axes: the place of a path, the polarity
}
type Entity = {
    readonly id: string
    readonly shape: string // the axis "shape"
    readonly type: string
    readonly vars: Readonly<Record<string, Var>>
    readonly items: readonly string[]
    readonly specs: readonly Spec[]
}

const CONFIGS: Readonly<Record<string, Config>> = {
    none: { text: '', run: '' },
    d0: { text: '{ depth: 0 }', run: '{ depth: 0 }' },
    d1: { text: '{ depth: 1 }', run: '{ depth: 1 }' },
    partial: { text: '{ allowPartial: true }', run: '{ allowPartial: true }' },
    bnd: {
        text: '{ enforceBoundary: true }',
        run: '{ enforceBoundary: true }',
    },
    d1bnd: {
        text: '{ depth: 1, enforceBoundary: true }',
        run: '{ depth: 1, enforceBoundary: true }',
    },
    maybe: {
        text: 'cfg_maybe',
        run: 'undefined',
        pre: ['export const cfg_maybe = undefined as { depth: 1 } | undefined'],
    },
    maybeSet: {
        text: 'cfg_maybeSet',
        run: '{ depth: 1 }',
        pre: [
            'export const cfg_maybeSet = { depth: 1 } as { depth: 1 } | undefined',
        ],
    },
    any: {
        text: '{ depth: anyDepth }',
        run: '{ depth: undefined }',
        pre: ['export const anyDepth: any = undefined'],
    },
    narrow: {
        text: 'cfg_narrow',
        run: '{ depth: 1, enforceBoundary: true }',
        pre: [
            'export const cfg_narrowWide = { depth: 1, enforceBoundary: true } as const',
            'export const cfg_narrow: { depth: 1 } = cfg_narrowWide',
        ],
    },
}
const CORE = ['none', 'd0', 'd1', 'partial', 'bnd', 'd1bnd']
const VARIABLE = ['maybe', 'maybeSet', 'any', 'narrow']

const ENTITIES: Entity[] = []
const add = (e: Entity) => ENTITIES.push(e)

// plain components, a transform, a default, an attribute
const PLAIN_ITEMS = ['ok', 'nonote', 'blank', 'sep', 'blankNote', 'blankId']
add({
    id: 'plain',
    shape: 'plain',
    type: '{ petId: string; shelterId: string; name: string; note?: string }',
    vars: {
        ok: {
            declared: '$E',
            value: "{ petId: 'p1', shelterId: 's1', name: 'rex', note: 'n1' }",
            vk: 'typical',
        },
        nonote: {
            declared: '$E',
            value: "{ petId: 'p1', shelterId: 's1', name: 'rex' }",
            vk: 'optional-absent',
        },
        blank: {
            declared: '$E',
            value: "{ petId: 'p1', shelterId: 's1', name: '', note: 'n1' }",
            vk: 'empty-text',
        },
        sep: {
            declared: '$E',
            value: "{ petId: 'p1', shelterId: 's1', name: 'a#b', note: 'n1' }",
            vk: 'separator-text',
        },
        blankNote: {
            declared: '$E',
            value: "{ petId: 'p1', shelterId: 's1', name: 'rex', note: '' }",
            vk: 'empty-text',
        },
        blankId: {
            declared: '$E',
            value: "{ petId: '', shelterId: 's1', name: 'rex', note: 'n1' }",
            vk: 'empty-text',
        },
        chSN: {
            declared: '{ shelterId: string; name: string }',
            value: "{ shelterId: 's2', name: 'n2' }",
            vk: 'typical',
        },
        chName: {
            declared: '{ name: string }',
            value: "{ name: 'n2' }",
            vk: 'block-part',
        },
        chNote: {
            declared: '{ note: string }',
            value: "{ note: 'n2' }",
            vk: 'typical',
        },
        chNone: { declared: '{}', value: '{}', vk: 'no-attribute' },
        chGhost: {
            declared: '{ note: string; ghost: number }',
            value: "{ note: 'n2', ghost: 1 }",
            vk: 'unheld-name',
        },
        sFirst: {
            declared: '{ shelterId: string }',
            value: "{ shelterId: 's1' }",
            vk: 'prefix',
        },
        sLit: {
            declared: "{ shelterId: 's1' }",
            value: "{ shelterId: 's1' }",
            vk: 'prefix-literal',
        },
        none: { declared: '{}', value: '{}', vk: 'no-attribute' },
        nameOnly: {
            declared: '{ name: string }',
            value: "{ name: 'rex' }",
            vk: 'prefix',
        },
        pidOnly: {
            declared: '{ petId: string }',
            value: "{ petId: 'p1' }",
            vk: 'prefix',
        },
    },
    items: PLAIN_ITEMS,
    specs: [
        {
            id: 'list2',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: ['shelterId', 'name'] }",
            keys: ['SK'],
            keyArgs: ['ok', 'blank', 'sep', 'sFirst', 'sLit', 'none'],
            configs: [...CORE, ...VARIABLE],
            items: PLAIN_ITEMS,
            changes: ['chSN', 'chName', 'chNote', 'chNone'],
        },
        {
            id: 'roleKeys',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: ['shelterId', 'name'] }",
            options: "{ key: { partition: 'PK', sort: 'SK' } }",
            items: ['ok', 'blank'],
            args: ['ok', 'nonote', 'blank', 'sep', 'none', 'pidOnly'],
            calls: ['keys', 'keyCondition'],
        },
        {
            id: 'indexKeys',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: ['shelterId', 'name'], GSI1PK: ['shelterId'], GSI1SK: ['name'] }",
            options:
                "{ key: { partition: 'PK', sort: 'SK' }, indexes: { G1: { partition: 'GSI1PK', sort: 'GSI1SK' } } }",
            items: ['ok', 'blank'],
            args: ['ok', 'blank', 'sep', 'none', 'pidOnly'],
            calls: ['keyCondition', 'keyConditionIndex'],
            indexes: ['G1'],
        },
        {
            id: 'codecItem',
            form: 'list',
            codec: 'record',
            schema: "{ PK: ['petId'], SK: ['shelterId', 'name'] }",
            options:
                "{ key: { partition: 'PK', sort: 'SK' }, codec: { petId: string, shelterId: string, name: string, note: optional(string) } }",
            items: ['ok', 'nonote', 'blank', 'sep'],
            args: ['ok', 'blank', 'none'],
            patches: ['chNote', 'chName', 'chNone', 'chGhost'],
            calls: ['keys', 'toItem', 'fromItem', 'encodePartial'],
        },
        {
            id: 'pkList',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['shelterId', 'petId'] }",
            keys: ['PK'],
            keyArgs: ['ok', 'blankId', 'sFirst', 'sLit', 'none'],
            configs: CORE,
            items: ['ok', 'blankId'],
        },
        {
            id: 'listOne',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: ['name'] }",
            keys: ['SK', 'PK'],
            keyArgs: ['ok', 'blank', 'sep', 'none', 'nameOnly', 'pidOnly'],
            configs: ['none', 'd0', 'partial'],
            items: PLAIN_ITEMS,
        },
        {
            id: 'attrNote',
            form: 'attr',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: 'note' }",
            keys: ['SK'],
            keyArgs: ['ok', 'nonote', 'blankNote'],
            configs: ['none'],
            items: PLAIN_ITEMS,
            changes: ['chNote', 'chNone'],
        },
        {
            id: 'attrName',
            form: 'attr',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: 'name' }",
            keys: ['SK'],
            keyArgs: ['ok', 'blank', 'sep'],
            configs: ['none'],
            items: PLAIN_ITEMS,
        },
        {
            id: 'tagTf',
            form: 'transform',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['name', (n: string) => ({ tag: 'T', value: n })]] }",
            keys: ['SK'],
            keyArgs: ['ok', 'blank', 'none'],
            configs: ['none', 'partial'],
            items: PLAIN_ITEMS,
        },
        {
            id: 'taglessTf',
            form: 'transform',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['name', (n: string) => ({ value: n })]] }",
            keys: ['SK'],
            keyArgs: ['ok', 'blank'],
            configs: ['none'],
            items: ['ok', 'blank', 'sep'],
        },
        {
            id: 'tagOpts',
            form: 'transform-options',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['name', { tag: 'NM' }]] }",
            keys: ['SK'],
            keyArgs: ['ok', 'blank'],
            configs: ['none'],
            items: ['ok', 'blank'],
        },
        {
            id: 'defaultFn',
            form: 'default-function',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['note', (n: string) => ({ value: n }), 'x']] }",
            keys: ['SK'],
            keyArgs: ['ok', 'nonote'],
            configs: ['none'],
            items: ['ok', 'nonote'],
            changes: ['chNote'],
        },
        {
            id: 'defaultOpts',
            form: 'default-options',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['note', { tag: 'DOSE' }, 'x']] }",
            keys: ['SK'],
            keyArgs: ['ok', 'nonote'],
            configs: ['none'],
            items: ['ok', 'nonote'],
        },
    ],
})

// a path below an optional object
add({
    id: 'opt',
    shape: 'optional-object',
    type: '{ petId: string; owner?: { id: string } }',
    vars: {
        owned: {
            declared: '$E',
            value: "{ petId: 'p1', owner: { id: 'o1' } }",
            vk: 'typical',
        },
        unowned: {
            declared: '$E',
            value: "{ petId: 'p2' }",
            vk: 'object-absent',
        },
        blankOwner: {
            declared: '$E',
            value: "{ petId: 'p3', owner: { id: '' } }",
            vk: 'empty-text',
        },
        ownedLit: {
            declared: '{ owner: { id: string } }',
            value: "{ owner: { id: 'o1' } }",
            vk: 'prefix',
        },
    },
    items: ['owned', 'unowned', 'blankOwner'],
    specs: [
        {
            id: 'pathAttr',
            form: 'path',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: 'owner.id' }",
            keys: ['SK'],
            keyArgs: ['owned', 'unowned', 'blankOwner', 'ownedLit'],
            configs: ['none'],
            items: ['owned', 'unowned', 'blankOwner'],
        },
        {
            id: 'pathList',
            form: 'path-list',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: ['owner.id'] }",
            keys: ['SK'],
            keyArgs: ['owned', 'unowned', 'ownedLit'],
            configs: ['none'],
            items: ['owned', 'unowned'],
        },
        {
            id: 'pathDefault',
            form: 'path-default',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['owner.id', (id: string) => ({ value: id }), 'none']] }",
            keys: ['SK'],
            keyArgs: ['owned', 'unowned'],
            configs: ['none'],
            items: ['owned', 'unowned'],
        },
        {
            id: 'pathDefaultOpts',
            form: 'default-options',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['owner.id', { tag: 'ID' }, 'none']] }",
            keys: ['SK'],
            keyArgs: ['owned', 'unowned'],
            configs: ['none'],
            items: ['owned', 'unowned'],
        },
    ],
})

// a path below a required object, with an options object
add({
    id: 'nest',
    shape: 'required-object',
    type: '{ petId: string; shelter: { code: string } }',
    vars: {
        ok: {
            declared: '$E',
            value: "{ petId: 'p1', shelter: { code: 'S' } }",
            vk: 'typical',
        },
        blankCode: {
            declared: '$E',
            value: "{ petId: 'p1', shelter: { code: '' } }",
            vk: 'empty-text',
        },
    },
    items: ['ok', 'blankCode'],
    specs: [
        {
            id: 'pathTag',
            form: 'transform-options',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['shelter.code', { tag: 'AT' }], 'petId'] }",
            keys: ['SK'],
            keyArgs: ['ok', 'blankCode'],
            configs: ['none', 'partial'],
            items: ['ok', 'blankCode'],
        },
        {
            id: 'pathTagDefault',
            form: 'default-options',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [['shelter.code', { tag: 'AT' }, 'x']] }",
            keys: ['SK'],
            keyArgs: ['ok'],
            configs: ['none'],
            items: ['ok'],
        },
        {
            id: 'pathPlain',
            form: 'path',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: ['shelter.code'] }",
            keys: ['SK'],
            keyArgs: ['ok', 'blankCode'],
            configs: ['none'],
            items: ['ok', 'blankCode'],
        },
    ],
})

// a path into a union of objects
add({
    id: 'doc',
    shape: 'union-of-objects',
    type: "{ id: string; meta: { kind: 'a'; a: string } | { kind: 'b'; b: string } }",
    vars: {
        a: {
            declared: '$E',
            value: "{ id: 'd1', meta: { kind: 'a', a: 'x' } }",
            vk: 'typical',
        },
        b: {
            declared: '$E',
            value: "{ id: 'd2', meta: { kind: 'b', b: 'x' } }",
            vk: 'option-lacks-name',
        },
    },
    items: ['a', 'b'],
    specs: [
        {
            id: 'pathList',
            form: 'path-list',
            codec: 'none',
            schema: "{ PK: ['id'], SK: ['meta.a'] }",
            keys: ['SK'],
            keyArgs: ['a', 'b'],
            configs: ['none'],
            items: ['a', 'b'],
        },
        {
            id: 'pathAttr',
            form: 'path',
            codec: 'none',
            schema: "{ PK: ['id'], SK: 'meta.a' }",
            keys: ['SK'],
            keyArgs: ['a', 'b'],
            configs: ['none'],
            items: ['a', 'b'],
        },
    ],
})

// a name with a `.` beside the object of the path, and the changes of keyUpdates
add({
    id: 'dotted',
    shape: 'dotted-name',
    type: "{ petId: string; 'owner.name': number; owner: { name: string } }",
    vars: {
        both: {
            declared: '$E',
            value: "{ petId: 'p1', 'owner.name': 8, owner: { name: 'bea' } }",
            vk: 'dotted-name',
        },
        chNum: {
            declared: "{ 'owner.name': number }",
            value: "{ 'owner.name': 8 }",
            vk: 'dotted-name',
        },
        chStr: {
            declared: "{ 'owner.name': string }",
            value: "{ 'owner.name': 'bea' }",
            vk: 'dotted-name',
        },
        chObj: {
            declared: '{ owner: { name: string } }',
            value: "{ owner: { name: 'bea' } }",
            vk: 'typical',
        },
        chBoth: {
            declared: "{ owner: { name: string }; 'owner.name': number }",
            value: "{ owner: { name: 'bea' }, 'owner.name': 8 }",
            vk: 'dotted-name',
        },
        chGhost: {
            declared: '{ ghost: number }',
            value: '{ ghost: 1 }',
            vk: 'unheld-name',
        },
        chNone: { declared: '{}', value: '{}', vk: 'no-attribute' },
    },
    items: ['both'],
    specs: [
        {
            id: 'dottedList',
            form: 'path-list',
            codec: 'none',
            schema: "{ PK: ['petId'], GSI1SK: ['owner.name'] }",
            keys: ['GSI1SK'],
            keyArgs: ['both'],
            configs: ['none'],
            items: ['both'],
            changes: ['chNum', 'chStr', 'chObj', 'chBoth', 'chGhost', 'chNone'],
        },
    ],
})

// a component whose name is a number
add({
    id: 'numname',
    shape: 'number-name',
    type: '{ 0: string; petId: string }',
    vars: {
        zero: {
            declared: '$E',
            value: "{ 0: 'zero', petId: 'p' }",
            vk: 'number-name',
        },
        zeroArg: {
            declared: '{ 0: string }',
            value: "{ 0: 'zero' }",
            vk: 'number-name',
        },
    },
    items: ['zero'],
    specs: [
        {
            id: 'numList',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: [0] }",
            keys: ['SK'],
            keyArgs: ['zero', 'zeroArg'],
            configs: ['none'],
            items: ['zero'],
        },
    ],
})

// the changes of keyUpdates, with a table key
add({
    id: 'kennel',
    shape: 'table-key',
    type: '{ petId: string; age: number }',
    vars: {
        ok: { declared: '$E', value: "{ petId: 'p1', age: 5 }", vk: 'typical' },
        chAge: {
            declared: '{ age: number }',
            value: '{ age: 5 }',
            vk: 'typical',
        },
        chWide: {
            declared: '{ age: number }',
            value: "{ age: 5, petId: 'p2' }",
            vk: 'extra-member',
            wide: true,
        },
        chBoth: {
            declared: '{ age: number; petId: string }',
            value: "{ age: 5, petId: 'p2' }",
            vk: 'table-key-named',
        },
        chPet: {
            declared: '{ petId: string }',
            value: "{ petId: 'p2' }",
            vk: 'table-key-named',
        },
        chExtra: {
            declared: '{ age: number }',
            value: "{ age: 5, note: 'x' }",
            vk: 'extra-member',
            wide: true,
        },
        ghostArg: {
            declared: '{ petId: string; ghost: number }',
            value: "{ petId: 'p1', ghost: 1 }",
            vk: 'unheld-name',
        },
    },
    items: ['ok'],
    specs: [
        {
            id: 'roles',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'], GSI1PK: ['age'] }",
            options: "{ key: { partition: 'PK' } }",
            keys: ['GSI1PK', 'PK'],
            keyArgs: ['ok', 'ghostArg'],
            configs: ['none'],
            items: ['ok'],
            changes: ['chAge', 'chWide', 'chExtra', 'chBoth', 'chPet'],
        },
    ],
})

// a literal that names no arm
add({
    id: 'noarm',
    shape: 'match-noarm',
    type: "{ petId: string; kind: 'CAT' | 'DOG' | 'FISH'; kennel: string }",
    vars: {
        cat: {
            declared: '$E',
            value: "{ petId: 'p1', kind: 'CAT', kennel: 'k1' }",
            vk: 'typical',
        },
        fish: {
            declared: '$E',
            value: "{ petId: 'p2', kind: 'FISH', kennel: 'k2' }",
            vk: 'literal-names-no-arm',
        },
        tagFish: {
            declared: "{ kind: 'FISH' }",
            value: "{ kind: 'FISH' }",
            vk: 'literal-names-no-arm',
        },
    },
    items: ['cat', 'fish'],
    specs: [
        {
            id: 'spec',
            form: 'match-spec',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: { discriminator: 'kind', spec: { CAT: ['kennel'], DOG: ['kennel'] } } }",
            keys: ['SK'],
            keyArgs: ['cat', 'fish', 'tagFish'],
            configs: ['none'],
            items: ['cat', 'fish'],
        },
        {
            id: 'plainPk',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['petId'] }",
            keys: ['PK'],
            keyArgs: ['cat', 'fish'],
            configs: ['none'],
            items: ['cat', 'fish'],
        },
        {
            id: 'cases',
            form: 'match-cases',
            codec: 'none',
            schema: "{ PK: ['petId'], SK: { discriminator: 'kind', cases: [[['CAT', 'DOG'], ['kennel']]] } }",
            keys: ['SK'],
            keyArgs: ['cat', 'fish'],
            configs: ['none'],
            items: ['cat', 'fish'],
        },
    ],
})

// refusals that the key shares with another rule
add({
    id: 'nullableMeta',
    shape: 'nullable-object',
    type: '{ id: string; meta: { note: string } | null }',
    vars: {
        noted: {
            declared: '$E',
            value: "{ id: 'i1', meta: { note: 'n' } }",
            vk: 'typical',
        },
        nulled: {
            declared: '$E',
            value: "{ id: 'i2', meta: null }",
            vk: 'object-absent',
        },
    },
    items: ['noted', 'nulled'],
    specs: [
        {
            id: 'codecPath',
            form: 'path-list',
            codec: 'record',
            schema: "{ PK: ['id'], SK: ['meta.note'] }",
            options:
                '{ codec: { id: string, meta: nullable(object({ note: string })) } }',
            keys: ['SK'],
            keyArgs: ['noted', 'nulled'],
            configs: ['none'],
            items: ['noted', 'nulled'],
        },
        {
            id: 'plainId',
            form: 'list',
            codec: 'none',
            schema: "{ PK: ['id'] }",
            keys: ['PK'],
            keyArgs: ['noted', 'nulled'],
            configs: ['none'],
            items: ['noted', 'nulled'],
        },
        {
            id: 'noCodec',
            form: 'path-list',
            codec: 'none',
            schema: "{ PK: ['id'], SK: ['meta.note'] }",
            keys: ['SK'],
            keyArgs: ['noted', 'nulled'],
            configs: ['none'],
            items: ['noted', 'nulled'],
        },
    ],
})
add({
    id: 'flatdot',
    shape: 'dotted-name',
    type: "{ petId: string; 'owner.name': string }",
    vars: {
        one: {
            declared: '$E',
            value: "{ petId: 'p1', 'owner.name': 'bea' }",
            vk: 'dotted-name',
        },
    },
    items: ['one'],
    specs: [
        {
            id: 'attr',
            form: 'attr',
            codec: 'none',
            schema: "{ PK: ['petId'], GSI1PK: 'owner.name' }",
            keys: ['GSI1PK'],
            keyArgs: ['one'],
            configs: ['none'],
            items: ['one'],
        },
        {
            id: 'list',
            form: 'path-list',
            codec: 'none',
            schema: "{ PK: ['petId'], GSI1PK: ['owner.name'] }",
            keys: ['GSI1PK'],
            keyArgs: ['one'],
            configs: ['none'],
            items: ['one'],
        },
    ],
})
const ADOPTED_CAT =
    "{ petId: string; species: 'CAT'; status: 'IN' | 'OUT'; adopted: boolean }"
const ADOPTED_DOG =
    "{ petId: string; species: 'DOG'; status: 'IN'; adopted: boolean }"
const ADOPTED_VARS: Record<string, Var> = {
    catIn: {
        declared: ADOPTED_CAT,
        value: "{ petId: 'p1', species: 'CAT', status: 'IN', adopted: true }",
        vk: 'typical',
    },
    catOut: {
        declared: ADOPTED_CAT,
        value: "{ petId: 'p1', species: 'CAT', status: 'OUT', adopted: true }",
        vk: 'typical',
    },
    dog: {
        declared: ADOPTED_DOG,
        value: "{ petId: 'p2', species: 'DOG', status: 'IN', adopted: false }",
        vk: 'typical',
    },
}
add({
    id: 'held',
    shape: 'held-codec',
    type: `${ADOPTED_CAT} | ${ADOPTED_DOG}`,
    vars: ADOPTED_VARS,
    items: ['catIn', 'catOut', 'dog'],
    specs: [
        {
            id: 'attr',
            form: 'attr',
            codec: 'held',
            schema: "{ PK: ['petId'], SK: 'adopted' }",
            options: '{ codec: TaggedPets }',
            keys: ['SK'],
            keyArgs: ['catIn', 'dog'],
            configs: ['none'],
            items: ['catIn', 'catOut', 'dog'],
        },
        {
            id: 'oneLevel',
            form: 'match-spec',
            codec: 'held',
            schema: "{ PK: ['petId'], SK: { discriminator: 'species', spec: { CAT: 'adopted', DOG: null } } }",
            options: '{ codec: TaggedPets }',
            keys: ['SK'],
            keyArgs: ['catIn', 'catOut', 'dog'],
            configs: ['none'],
            items: ['catIn', 'catOut', 'dog'],
        },
        {
            id: 'twoLevels',
            form: 'match-nested',
            codec: 'held',
            schema: "{ PK: ['petId'], SK: { discriminator: 'species', spec: { CAT: { discriminator: 'status', spec: { IN: 'adopted', OUT: null } }, DOG: null } } }",
            options: '{ codec: TaggedPets }',
            keys: ['SK'],
            keyArgs: ['catIn', 'catOut', 'dog'],
            configs: ['none'],
            items: ['catIn', 'catOut', 'dog'],
        },
        {
            id: 'untagged',
            form: 'attr',
            codec: 'held',
            schema: "{ PK: ['petId'], SK: 'adopted' }",
            options: '{ codec: UntaggedPets }',
            keys: ['SK'],
            keyArgs: ['catIn'],
            configs: ['none'],
            items: ['catIn'],
        },
    ],
})

// the axes of the pool of A16-11: where the arm stands, and what the arm gives
const PET = "{ petId: string; kind: 'CAT'"
type Arm = { more: string; spec: string; codec: string; present: string | null }
const ARMS: Record<string, Arm> = {
    null: { more: '', spec: 'null', codec: '', present: null },
    attr: {
        more: ' nickname?: string;',
        spec: "'nickname'",
        codec: ', nickname: optional(string)',
        present: ", nickname: 'rex'",
    },
    path: {
        more: ' owner?: { id: string };',
        spec: "'owner.id'",
        codec: ', owner: optional(object({ id: string }))',
        present: ", owner: { id: 'o1' }",
    },
}
const tidy = (t: string) => t.replace(/;\s*}/g, ' }').replace(/;;/g, ';')
const armDraws = (): void => {
    for (const [armId, arm] of Object.entries(ARMS)) {
        const present = arm.present ?? ''
        const DOG = "{ petId: string; kind: 'DOG'; ownerId: string }"
        const DOGV = "{ petId: 'p1', kind: 'DOG', ownerId: 'o1' }"
        const DOG_CODEC =
            "object({ petId: string, kind: string('DOG'), ownerId: string })"
        // top
        if (armId !== 'path') {
            const topType =
                armId === 'null'
                    ? `${PET} }`
                    : '{ petId: string; nickname?: string }'
            const topSpec = armId === 'null' ? 'null' : "'nickname'"
            add({
                id: `top_${armId}`,
                shape: 'arm-top',
                type: topType,
                vars: {
                    bare: {
                        declared: '$E',
                        value:
                            armId === 'null'
                                ? "{ petId: 'p1', kind: 'CAT' }"
                                : "{ petId: 'p1' }",
                        vk: 'key-absent',
                    },
                    ...(armId === 'null'
                        ? {}
                        : {
                              named: {
                                  declared: '$E',
                                  value: "{ petId: 'p1', nickname: 'rex' }",
                                  vk: 'typical',
                              },
                          }),
                },
                items: armId === 'null' ? ['bare'] : ['bare', 'named'],
                specs: [
                    {
                        id: 'spec',
                        form: `arm-${armId}`,
                        codec: 'none',
                        schema: `{ PK: ['petId'], SK: ${topSpec} }`,
                        keys: ['SK'],
                        keyArgs:
                            armId === 'null' ? ['bare'] : ['bare', 'named'],
                        configs: ['none'],
                        items: armId === 'null' ? ['bare'] : ['bare', 'named'],
                    },
                ],
            })
        }
        // union
        const cat = tidy(`{ petId: string; kind: 'CAT';${arm.more} }`)
        const unionVars: Record<string, Var> = {
            cat: {
                declared: cat,
                value: "{ petId: 'p1', kind: 'CAT' }",
                vk: 'key-absent',
            },
            dog: { declared: DOG, value: DOGV, vk: 'typical' },
            ...(arm.present
                ? {
                      catFull: {
                          declared: cat,
                          value: `{ petId: 'p1', kind: 'CAT'${present} }`,
                          vk: 'typical',
                      },
                  }
                : {}),
        }
        const unionItems = Object.keys(unionVars)
        unionVars.chCat = {
            declared: "{ kind: 'CAT' }",
            value: "{ kind: 'CAT' }",
            vk: 'discriminator-only',
        }
        const unionChanges = ['chCat']
        if (arm.present) {
            const field =
                armId === 'attr' ? 'nickname: string' : 'owner: { id: string }'
            unionVars.chCatFull = {
                declared: `{ kind: 'CAT'; ${field} }`,
                value: `{ kind: 'CAT'${present} }`,
                vk: 'typical',
            }
            unionChanges.push('chCatFull')
        }
        add({
            id: `union_${armId}`,
            shape: 'arm-union',
            type: `${DOG} | ${cat}`,
            vars: unionVars,
            items: unionItems,
            specs: ['none', 'tagged'].map((c) => ({
                id: c,
                form: `arm-${armId}`,
                codec: c === 'none' ? 'none' : 'tagged',
                schema: `{ PK: ['petId'], SK: { discriminator: 'kind', spec: { DOG: ['ownerId'], CAT: ${arm.spec} } } }`,
                options:
                    c === 'none'
                        ? undefined
                        : `{ codec: item(discriminatedUnion('kind', [${DOG_CODEC}, object({ petId: string, kind: string('CAT')${arm.codec} })])) }`,
                keys: ['SK'],
                keyArgs: unionItems,
                configs: ['none'],
                items: unionItems,
                changes: unionChanges,
            })),
        })
        // literal
        const stay = (status: string) =>
            tidy(
                `{ petId: string; status: ${status}; kennel: string;${arm.more} }`,
            )
        const litVars: Record<string, Var> = {
            out: {
                declared: stay("'OUT'"),
                value: "{ petId: 'p1', status: 'OUT', kennel: 'k1' }",
                vk: 'key-absent',
            },
            in: {
                declared: stay("'IN'"),
                value: "{ petId: 'p1', status: 'IN', kennel: 'k1' }",
                vk: 'typical',
            },
            ...(arm.present
                ? {
                      outFull: {
                          declared: stay("'OUT'"),
                          value: `{ petId: 'p1', status: 'OUT', kennel: 'k1'${present} }`,
                          vk: 'typical',
                      },
                  }
                : {}),
        }
        const litItems = Object.keys(litVars)
        add({
            id: `literal_${armId}`,
            shape: 'arm-literal',
            type: stay("'IN' | 'OUT'"),
            vars: litVars,
            items: litItems,
            specs: ['none', 'record'].map((c) => ({
                id: c,
                form: `arm-${armId}`,
                codec: c === 'none' ? 'none' : 'record',
                schema: `{ PK: ['petId'], SK: { discriminator: 'status', spec: { IN: ['kennel'], OUT: ${arm.spec} } } }`,
                options:
                    c === 'none'
                        ? undefined
                        : `{ codec: { petId: string, status: string('IN', 'OUT'), kennel: string${arm.codec} } }`,
                keys: ['SK'],
                keyArgs: litItems,
                configs: ['none'],
                items: litItems,
            })),
        })
        // nested
        if (armId !== 'path') {
            const ncat = tidy(
                `{ petId: string; kind: 'CAT'; status: 'IN' | 'OUT'; kennel: string;${arm.more} }`,
            )
            const ncatAt = (status: string) =>
                tidy(
                    `{ petId: string; kind: 'CAT'; status: ${status}; kennel: string;${arm.more} }`,
                )
            const ndog = "{ petId: string; kind: 'DOG' }"
            const nVars: Record<string, Var> = {
                catOut: {
                    declared: ncatAt("'OUT'"),
                    value: "{ petId: 'p1', kind: 'CAT', status: 'OUT', kennel: 'k1' }",
                    vk: 'key-absent',
                },
                catIn: {
                    declared: ncatAt("'IN'"),
                    value: "{ petId: 'p1', kind: 'CAT', status: 'IN', kennel: 'k1' }",
                    vk: 'typical',
                },
                dog: {
                    declared: ndog,
                    value: "{ petId: 'p1', kind: 'DOG' }",
                    vk: 'key-absent',
                },
            }
            add({
                id: `nested_${armId}`,
                shape: 'arm-nested',
                type: `${ncat} | ${ndog}`,
                vars: nVars,
                items: Object.keys(nVars),
                specs: ['none', 'tagged'].map((c) => ({
                    id: c,
                    form: `arm-${armId}`,
                    codec: c === 'none' ? 'none' : 'tagged',
                    schema: `{ PK: ['petId'], SK: { discriminator: 'kind', spec: { CAT: { discriminator: 'status', spec: { IN: ['kennel'], OUT: ${arm.spec} } }, DOG: null } } }`,
                    options:
                        c === 'none'
                            ? undefined
                            : `{ codec: item(discriminatedUnion('kind', [object({ petId: string, kind: string('CAT'), status: string('IN', 'OUT'), kennel: string${arm.codec} }), object({ petId: string, kind: string('DOG') })])) }`,
                    keys: ['SK'],
                    keyArgs: Object.keys(nVars),
                    configs: ['none'],
                    items: Object.keys(nVars),
                })),
            })
        }
    }
}
armDraws()

// the axes of the pool of A16-12: the kind of the discriminator, the place of a path, the form, the polarity
const OWNER = 'owner: { id: string }'
type Kind = {
    readonly members: readonly string[]
    readonly disc: string
    readonly arms: readonly (readonly [readonly string[], string])[]
    readonly values: readonly (readonly [string, number, string, string])[] // label, member, literal, the axis "value"
    readonly lacking: string
    readonly absent?: boolean // the discriminator can be absent: the type refuses each table of the kind at the discriminator
}
const KINDS: Record<string, Kind> = {
    single: {
        members: [
            `{ petId: string; kind: 'CAT'; kennel: string; ${OWNER} }`,
            `{ petId: string; kind: 'DOG'; ownerId: string; ${OWNER} }`,
        ],
        disc: 'kind',
        arms: [
            [['CAT'], 'kennel'],
            [['DOG'], 'ownerId'],
        ],
        values: [
            [
                'cat',
                0,
                "{ petId: 'p1', kind: 'CAT', kennel: 'k1', owner: { id: 'o1' } }",
                'typical',
            ],
            [
                'dog',
                1,
                "{ petId: 'p2', kind: 'DOG', ownerId: 'u2', owner: { id: 'o2' } }",
                'typical',
            ],
        ],
        lacking: 'ownerId',
    },
    double: {
        members: [
            `{ petId: string; status: 'IN' | 'OUT'; kennel: string; ${OWNER} }`,
        ],
        disc: 'status',
        arms: [
            [['IN'], 'kennel'],
            [['OUT'], 'petId'],
        ],
        values: [
            [
                'in',
                0,
                "{ petId: 'p1', status: 'IN', kennel: 'k1', owner: { id: 'o1' } }",
                'two-literal-member',
            ],
            [
                'out',
                0,
                "{ petId: 'p2', status: 'OUT', kennel: 'k2', owner: { id: 'o2' } }",
                'two-literal-member',
            ],
        ],
        lacking: 'ownerId',
    },
    mixed: {
        members: [
            `{ petId: string; kind: 'CAT' | 'BIRD'; kennel: string; ${OWNER} }`,
            `{ petId: string; kind: 'DOG'; ownerId: string; ${OWNER} }`,
        ],
        disc: 'kind',
        arms: [
            [['CAT', 'BIRD'], 'kennel'],
            [['DOG'], 'ownerId'],
        ],
        values: [
            [
                'cat',
                0,
                "{ petId: 'p1', kind: 'CAT', kennel: 'k1', owner: { id: 'o1' } }",
                'two-literal-member',
            ],
            [
                'bird',
                0,
                "{ petId: 'p3', kind: 'BIRD', kennel: 'k3', owner: { id: 'o3' } }",
                'two-literal-member',
            ],
            [
                'dog',
                1,
                "{ petId: 'p2', kind: 'DOG', ownerId: 'u2', owner: { id: 'o2' } }",
                'typical',
            ],
        ],
        lacking: 'ownerId',
    },
    optional: {
        members: [
            `{ petId: string; kind?: 'CAT'; kennel: string; ${OWNER} }`,
            `{ petId: string; kind: 'DOG'; ownerId: string; ${OWNER} }`,
        ],
        disc: 'kind',
        arms: [
            [['CAT'], 'kennel'],
            [['DOG'], 'ownerId'],
        ],
        values: [
            [
                'cat',
                0,
                "{ petId: 'p1', kind: 'CAT', kennel: 'k1', owner: { id: 'o1' } }",
                'typical',
            ],
            [
                'nokind',
                0,
                "{ petId: 'p4', kennel: 'k4', owner: { id: 'o4' } }",
                'discriminator-absent',
            ],
            [
                'dog',
                1,
                "{ petId: 'p2', kind: 'DOG', ownerId: 'u2', owner: { id: 'o2' } }",
                'typical',
            ],
        ],
        lacking: 'ownerId',
        absent: true,
    },
    lacking: {
        members: [
            `{ petId: string; kind: 'CAT'; kennel: string; ${OWNER} }`,
            `{ petId: string; ownerId: string; ${OWNER} }`,
        ],
        disc: 'kind',
        arms: [[['CAT'], 'kennel']],
        values: [
            [
                'cat',
                0,
                "{ petId: 'p1', kind: 'CAT', kennel: 'k1', owner: { id: 'o1' } }",
                'typical',
            ],
            [
                'nokind',
                1,
                "{ petId: 'p4', ownerId: 'u4', owner: { id: 'o4' } }",
                'discriminator-absent',
            ],
        ],
        lacking: 'ownerId',
        absent: true,
    },
    dpath: {
        members: [
            `{ petId: string; meta: { kind: 'CAT' }; kennel: string; ${OWNER} }`,
            `{ petId: string; meta: { kind: 'DOG' }; ownerId: string; ${OWNER} }`,
        ],
        disc: 'meta.kind',
        arms: [
            [['CAT'], 'kennel'],
            [['DOG'], 'ownerId'],
        ],
        values: [
            [
                'cat',
                0,
                "{ petId: 'p1', meta: { kind: 'CAT' }, kennel: 'k1', owner: { id: 'o1' } }",
                'typical',
            ],
            [
                'dog',
                1,
                "{ petId: 'p2', meta: { kind: 'DOG' }, ownerId: 'u2', owner: { id: 'o2' } }",
                'typical',
            ],
        ],
        lacking: 'ownerId',
    },
    // one option that holds two literals at the path of the discriminator
    dpathdouble: {
        members: [
            `{ petId: string; meta: { status: 'IN' | 'OUT' }; kennel: string; ${OWNER} }`,
        ],
        disc: 'meta.status',
        arms: [
            [['IN'], 'kennel'],
            [['OUT'], 'petId'],
        ],
        values: [
            [
                'in',
                0,
                "{ petId: 'p1', meta: { status: 'IN' }, kennel: 'k1', owner: { id: 'o1' } }",
                'two-literal-member',
            ],
            [
                'out',
                0,
                "{ petId: 'p2', meta: { status: 'OUT' }, kennel: 'k2', owner: { id: 'o2' } }",
                'two-literal-member',
            ],
        ],
        lacking: 'ownerId',
    },
}
const armText = (names: readonly string[]) =>
    `[${names.map((n) => `'${n}'`).join(', ')}]`
const matchText = (
    disc: string,
    arms: readonly (readonly [readonly string[], readonly string[]])[],
    form: string,
) =>
    form === 'spec'
        ? `{ discriminator: '${disc}', spec: { ${arms.flatMap(([lits, names]) => lits.map((l) => `${l}: ${armText(names)}`)).join(', ')} } }`
        : `{ discriminator: '${disc}', cases: [${arms.map(([lits, names]) => `[[${lits.map((l) => `'${l}'`).join(', ')}], ${armText(names)}]`).join(', ')}] }`
const tagOf = (disc: string, value: string): string | null => {
    const leaf = disc.split('.').at(-1) as string
    const m = new RegExp(`\\b${leaf}: ('[A-Z]+')`).exec(value)
    if (!m) return null
    // the object that holds the literal at the path of the discriminator
    return disc
        .split('.')
        .reduceRight((inner, name) => `{ ${name}: ${inner} }`, m[1] as string)
}
for (const [kindId, kind] of Object.entries(KINDS)) {
    const vars: Record<string, Var> = {}
    for (const [label, member, value, vk] of kind.values) {
        vars[label] = { declared: kind.members[member] as string, value, vk }
        const tag = tagOf(kind.disc, value)
        if (tag)
            vars[`tag_${label}`] = {
                declared: tag,
                value: tag,
                vk: `${vk}-tag-only`,
            }
    }
    const labels = kind.values.map((v) => v[0])
    const keyArgs = Object.keys(vars)
    const specs: Spec[] = []
    for (const place of ['nopath', 'armpath', 'otherpath'])
        for (const form of ['spec', 'cases'])
            for (const pole of ['pos', 'neg']) {
                const first = [
                    pole === 'neg'
                        ? kind.lacking
                        : (
                              kind.arms[0] as readonly [
                                  readonly string[],
                                  string,
                              ]
                          )[1],
                ]
                const firstNames =
                    place === 'armpath' ? [...first, 'owner.id'] : first
                const drawn = [
                    [
                        (
                            kind.arms[0] as readonly [readonly string[], string]
                        )[0],
                        firstNames,
                    ] as const,
                    ...kind.arms
                        .slice(1)
                        .map(([lits, name]) => [lits, [name]] as const),
                ]
                const pk = place === 'otherpath' ? "['owner.id']" : "['petId']"
                specs.push({
                    id: `${place}_${form}_${pole}`,
                    extra: { place, pole },
                    form: `match-${form}`,
                    codec: 'none',
                    schema: `{ PK: ${pk}, SK: ${matchText(kind.disc, drawn, form)} }`,
                    keys: ['SK'],
                    keyArgs,
                    configs: ['none'],
                    items: labels,
                    // A discriminator that can be absent breaks its rule in both poles, and the cases form
                    // refuses it there. The negative pole of another kind names an attribute that no option
                    // holds: the error starts at the name.
                    ...(kind.absent === true
                        ? pole === 'neg' || form === 'cases'
                            ? {
                                  at: `discriminator: '${kind.disc}'`,
                                  rule: 'can be absent',
                              }
                            : {}
                        : pole === 'neg'
                          ? {
                                at: `'${kind.lacking}'`,
                                rule: 'is no name or path of the entity',
                            }
                          : {}),
                })
            }
    specs.push({
        id: 'plainPk',
        form: 'list',
        codec: 'none',
        schema: "{ PK: ['petId'] }",
        keys: ['PK'],
        keyArgs: Object.keys(vars),
        configs: ['none'],
        items: labels,
    })
    specs.push({
        id: 'nullArms',
        form: 'match-null-arms',
        codec: 'none',
        schema: `{ PK: ['petId'], SK: { discriminator: '${kind.disc}', spec: { ${kind.arms.flatMap(([lits]) => lits.map((l) => `${l}: null`)).join(', ')} } } }`,
        keys: ['SK'],
        keyArgs: Object.keys(vars),
        configs: ['none'],
        items: labels,
    })
    add({
        id: `kind_${kindId}`,
        shape: `match-${kindId}`,
        type: kind.members.join(' | '),
        vars,
        items: labels,
        specs,
    })
}

// A draw with the option `separator` for one schema form: the first table of the form that holds no
// options. The type can refuse the copy at construction, as it refuses opt.pathList, and a refused
// table gives no method row. So each form of the list holds method rows except that one.
const SEPARATED = [
    'list2',
    'attrNote',
    'pathAttr',
    'pathList',
    'pathDefault',
    'tagTf',
    'defaultFn',
    'nopath_spec_pos',
    'nopath_cases_pos',
    'nullArms',
    'twoLevels',
]
{
    const seen = new Set<string>()
    ENTITIES.forEach((entity, at) => {
        const copies: Spec[] = []
        for (const spec of entity.specs) {
            if (
                !SEPARATED.includes(spec.id) ||
                (spec.options !== undefined && spec.id !== 'twoLevels') ||
                seen.has(spec.form) ||
                !(
                    entity.id === 'plain' ||
                    entity.id.startsWith('kind_single') ||
                    entity.id === 'opt' ||
                    entity.id === 'held'
                )
            )
                continue
            seen.add(spec.form)
            copies.push({
                ...spec,
                id: `${spec.id}_sep`,
                options:
                    spec.options === undefined
                        ? "{ separator: '|' }"
                        : spec.options.replace(/ }$/, ", separator: '|' }"),
            })
        }
        if (copies.length > 0)
            ENTITIES[at] = { ...entity, specs: [...entity.specs, ...copies] }
    })
}

// ---------------------------------------------------------------- the print

type Row = {
    id: string
    group: string
    expect: 'accept' | 'refuse'
    file: string
    line: number
    after?: string[]
    at?: string // the text where the first error of a refuse row must start
    rule?: string // a text that a library rule message of a refuse row must hold
    axes: Record<string, string>
    run?: string
}
// A text that carries a label of the key, as `PETID#p1`. Only such a text has a foreign value.
const labelled = (options: string | undefined): RegExp => {
    const separator = /separator: '(.)'/.exec(options ?? '')?.[1] ?? '#'
    return new RegExp(`^[A-Z0-9_]+\\${separator}`)
}
// A key that the run time does not write is foreign to a declared member only where every arm of the
// spec for that member gives no value: a `null` arm. An attribute or a path can hold a value in another item.
const forcesAbsence = (form: string) =>
    form === 'arm-null' || form === 'match-null-arms'
// A plain item: each leaf is a text of one character or more with no separator, or a number or a boolean.
// The type alone fixes such an item. An empty text, a text with the separator and a null are not plain.
export const plain = (value: unknown): boolean =>
    typeof value === 'string'
        ? value.length > 0 && !value.includes('#')
        : typeof value === 'number' || typeof value === 'boolean'
          ? true
          : value !== null &&
            typeof value === 'object' &&
            Object.values(value).every(plain)
const sha = (text: string) =>
    createHash('sha1').update(text).digest('hex').slice(0, 8)
// A value of the run time as a line of the program. An error value is a CodecError.
const exprOf = (value: unknown): string =>
    value instanceof CodecError
        ? `new CodecError(${JSON.stringify(value.reason)}, '${value.kind}')`
        : lit(value)
const showRun = (o: Outcome, group: string) =>
    o.ok
        ? group === 'construct'
            ? 'builds'
            : `ok ${exprOf(o.value).slice(0, 200)}`
        : `throw ${o.message}`

type Table = {
    readonly key: (name: string, item: object, config?: object) => unknown
    readonly toEntry: (item: object) => Record<string, unknown>
    readonly fromEntry: (entry: object) => unknown
    readonly keyUpdates: (change: object) => unknown
    readonly keys: (item: object) => unknown
    readonly keyCondition: (a: object | string, b?: object) => unknown
    readonly toItem: (item: object) => unknown
    readonly fromItem: (stored: object) => unknown
    readonly codec: { readonly encodePartial: (change: object) => unknown }
}

// The names are joined, so that no template cites a file that the tree does not hold.
const programName = (part: number) => ['entries', part].join('')
const programFile = (part: number) => [programName(part), '.ts'].join('')

export const printPool = (parts: number, reverse: boolean) => {
    const files: string[][] = Array.from({ length: parts }, () => [])
    const rows: Row[] = []
    const ids = new Set<string>()
    const runs: string[] = []
    const typed = new Set<string>()
    const declared: Set<string>[] = Array.from(
        { length: parts },
        () => new Set(),
    )
    const draws = ENTITIES.flatMap((e) => e.specs.map((s) => ({ e, s })))
    if (reverse) draws.reverse()
    const header = [
        '// The pool of the entry methods. Generated by lean.entry.spec.ts. One line is one decision of the run time.',
        "import type { StandardSchemaV1 } from '../../src/codec/standard'",
        "import { CodecError, discriminatedUnion, held, item, nullable, number, object, optional, string, union } from '../../src/codec/codec'",
        "import { tableEntry } from '../../src/Rotorise'",
        'export const library = { discriminatedUnion, held, item, nullable, number, object, optional, string, union }',
        ...PRELUDE.map(([n, t]) => `export const ${n} = ${t}`),
    ]
    for (const f of files) f.push(...header)
    for (const { e, s } of draws) {
        const hash = sha(`${e.type}|${s.schema}|${s.options ?? ''}`)
        const part = Number.parseInt(hash, 16) % parts
        const out = files[part] as string[]
        const decl = declared[part] as Set<string>
        const base: Record<string, string> = {
            shape: e.shape,
            form: s.form,
            codec: s.codec,
            ...s.extra,
        }
        const T = `T_${e.id}_${s.id}`
        const LAB = labelled(s.options)
        const emit = (line: string) => out.push(line)
        const row = (
            group: string,
            expect: 'accept' | 'refuse',
            text: string,
            line: string,
            axes: Record<string, string>,
            after?: string[],
            run?: Outcome,
            h = hash,
            site: { at?: string | undefined; rule?: string | undefined } = {},
        ): string => {
            const id = `${group}|${expect}|${h}|${text}`
            if (ids.has(id)) throw new Error(`duplicate row id ${id}`)
            ids.add(id)
            if (expect === 'refuse') emit('// @ts-expect-error')
            emit(line)
            const r: Row = {
                id,
                group,
                expect,
                file: programFile(part),
                line: out.length,
                axes: { ...base, ...axes },
            }
            if (after) r.after = after
            if (site.at !== undefined) r.at = site.at
            if (site.rule !== undefined) r.rule = site.rule
            if (run) {
                r.run = showRun(run, group)
                runs.push(`RUNROW ${id} ${r.run}`)
            }
            rows.push(r)
            return id
        }
        // the entity and its variables
        const E = `E_${e.id}`
        if (!decl.has(e.id)) {
            decl.add(e.id)
            emit(`export type ${E} = ${e.type}`)
            for (const [name, v] of Object.entries(e.vars)) {
                const declaredType = v.declared.replaceAll('$E', E)
                if (v.wide) {
                    emit(`export const w_${e.id}_${name} = ${v.value} as const`)
                    emit(
                        `export const v_${e.id}_${name}: ${declaredType} = w_${e.id}_${name}`,
                    )
                } else
                    emit(
                        `export const v_${e.id}_${name}: ${declaredType} = ${v.value}`,
                    )
            }
        }
        if (!typed.has(e.id)) {
            typed.add(e.id)
            for (const name of e.items)
                row(
                    'typing',
                    'accept',
                    `ty:${e.id}.${name}`,
                    `export const ty_${e.id}_${name}: ${E} = v_${e.id}_${name}`,
                    { value: (e.vars[name] as Var).vk },
                    undefined,
                    undefined,
                    sha(e.type),
                )
        }
        const make = tableEntry<Record<string, unknown>>() as unknown as (
            schema: unknown,
            options?: unknown,
        ) => Table
        const options = s.options ? ev(s.options) : undefined
        const made = attempt(() => make(ev(s.schema), options))
        // The oracle of a construct row: the construction throws, or toEntry throws for a plain item.
        const plainThrow = made.ok
            ? (s.items ?? [])
                  .map((name) => ({
                      name,
                      value: ev((e.vars[name] as Var).value),
                  }))
                  .filter((i) => plain(i.value))
                  .map((i) => ({
                      name: i.name,
                      out: attempt(() =>
                          (made.value as Table).toEntry(i.value as object),
                      ),
                  }))
                  .find((i) => !i.out.ok)
            : undefined
        const built: Outcome = plainThrow
            ? {
                  ok: false,
                  message: `toEntry throws for the plain item ${plainThrow.name}: ${(plainThrow.out as { message: string }).message}`,
              }
            : made
        const keyNames = Object.keys(ev(s.schema) as object)
        const cid = row(
            'construct',
            built.ok ? 'accept' : 'refuse',
            `${e.id}.${s.id}`,
            `export const ${T} = tableEntry<${E}>()(${s.schema}${s.options ? `, ${s.options}` : ''})`,
            {},
            undefined,
            built,
            hash,
            { at: s.at, rule: s.rule },
        )
        if (!built.ok) continue
        const table = made.ok ? (made.value as Table) : (undefined as never)
        let n = 0
        const call = (
            group: string,
            text: string,
            expr: string,
            run: Outcome,
            axes: Record<string, string>,
        ) => {
            const v = `c_${hash}_${n++}`
            const id = row(
                group,
                run.ok ? 'accept' : 'refuse',
                `${text}.call`,
                `export const ${v} = ${expr}`,
                axes,
                [cid],
                run,
                hash,
                // the argument is a variable of its declared type, and the error of a refused call starts there
                { at: /\b(?:v|si?)_\w+/.exec(expr)?.[0] },
            )
            return { v, id }
        }
        const result = (
            group: string,
            text: string,
            v: string,
            id: string,
            value: unknown,
            axes: Record<string, string>,
        ) =>
            row(
                group,
                'accept',
                `${text}.result`,
                `export const r_${v}: typeof ${v} = ${exprOf(value)}`,
                axes,
                [cid, id],
            )
        const foreign = (
            group: string,
            text: string,
            v: string,
            id: string,
            value: string,
            axes: Record<string, string>,
            tag: string,
        ) =>
            row(
                group,
                'refuse',
                `${text}.foreign${tag}`,
                `export const f_${v}_${sha(tag)}: typeof ${v} = ${value}`,
                axes,
                [cid, id],
                undefined,
                hash,
                // a foreign property holds one element, the property. The result of key and keyUpdates has no site.
                tag.startsWith(':') ? { at: `"${tag.slice(1)}"` } : {},
            )
        const entryRows = (
            group: string,
            text: string,
            v: string,
            id: string,
            entry: Record<string, unknown>,
            axes: Record<string, string>,
        ) => {
            result(group, text, v, id, entry, axes)
            for (const k of keyNames) {
                const held = entry[k]
                if (
                    typeof held === 'string'
                        ? !LAB.test(held)
                        : !forcesAbsence(s.form)
                )
                    continue
                const changed = {
                    ...entry,
                    [k]: typeof held === 'string' ? `~${held}` : '~#~',
                }
                foreign(group, text, v, id, lit(changed), axes, `:${k}`)
            }
        }
        const toEntryOf = new Map<string, Record<string, unknown>>()
        for (const name of s.items ?? []) {
            const vr = e.vars[name] as Var
            const axes = { value: vr.vk, arg: name, method: 'toEntry' }
            const run = attempt(() => table.toEntry(ev(vr.value) as object))
            const c = call(
                'toEntry',
                `${T}.toEntry(${name})`,
                `${T}.toEntry(v_${e.id}_${name})`,
                run,
                axes,
            )
            if (!run.ok) continue
            const entry = run.value as Record<string, unknown>
            toEntryOf.set(name, entry)
            entryRows(
                'toEntry',
                `${T}.toEntry(${name})`,
                c.v,
                c.id,
                entry,
                axes,
            )
            // infer: the entry type of the entity, against the same row
            const iv = `i_${hash}_${name}`
            const iid = row(
                'infer',
                'accept',
                `${T}.infer(${name}).result`,
                `export const ${iv}: typeof ${T}.infer = ${lit(entry)}`,
                { ...axes, method: 'infer' },
                [cid],
            )
            for (const k of keyNames) {
                const held = entry[k]
                if (
                    typeof held === 'string'
                        ? !LAB.test(held)
                        : !forcesAbsence(s.form)
                )
                    continue
                if (/attr|path/.test(s.form)) continue // another member of the union can hold any text at the key
                const changed = {
                    ...entry,
                    [k]: typeof held === 'string' ? `~${held}` : '~#~',
                }
                row(
                    'infer',
                    'refuse',
                    `${T}.infer(${name}).foreign:${k}`,
                    `export const if_${hash}_${name}_${sha(k)}: typeof ${T}.infer = ${lit(changed)}`,
                    { ...axes, method: 'infer' },
                    [cid, iid],
                    undefined,
                    hash,
                    { at: `"${k}"` },
                )
            }
            // fromEntry on the row that toEntry wrote, as a constant of its own type
            const fx = { ...axes, method: 'fromEntry' }
            const frun = attempt(() => table.fromEntry(entry))
            const sv = `s_${hash}_${name}`
            emit(`export const ${sv} = ${lit(entry)} as const`)
            const fc = call(
                'fromEntry',
                `${T}.fromEntry(${name})`,
                `${T}.fromEntry(${sv})`,
                frun,
                fx,
            )
            if (frun.ok) {
                result(
                    'fromEntry',
                    `${T}.fromEntry(${name})`,
                    fc.v,
                    fc.id,
                    frun.value,
                    fx,
                )
                const first = keyNames[0] as string
                foreign(
                    'fromEntry',
                    `${T}.fromEntry(${name})`,
                    fc.v,
                    fc.id,
                    lit({ ...(frun.value as object), [first]: '~' }),
                    fx,
                    `:${first}`,
                )
            }
        }
        for (const keyName of s.keys ?? []) {
            for (const argName of s.keyArgs ?? []) {
                const vr = e.vars[argName] as Var
                for (const cfgName of s.configs ?? ['none']) {
                    const cfg = CONFIGS[cfgName] as Config
                    for (const line of cfg.pre ?? [])
                        if (!out.includes(line)) emit(line)
                    const axes = {
                        value: vr.vk,
                        arg: argName,
                        cfg: cfgName,
                        method: 'key',
                    }
                    const run = attempt(() =>
                        cfg.run
                            ? table.key(
                                  keyName,
                                  ev(vr.value) as object,
                                  ev(cfg.run) as object,
                              )
                            : table.key(keyName, ev(vr.value) as object),
                    )
                    const text = `${T}.key(${keyName},${argName},${cfgName})`
                    const c = call(
                        'key',
                        text,
                        `${T}.key('${keyName}', v_${e.id}_${argName}${cfg.text ? `, ${cfg.text}` : ''})`,
                        run,
                        axes,
                    )
                    if (!run.ok) continue
                    result('key', text, c.v, c.id, run.value, axes)
                    if (
                        typeof run.value === 'string'
                            ? !LAB.test(run.value)
                            : !forcesAbsence(s.form)
                    )
                        continue
                    foreign(
                        'key',
                        text,
                        c.v,
                        c.id,
                        typeof run.value === 'string'
                            ? lit(`~${run.value}`)
                            : lit('~'),
                        axes,
                        '',
                    )
                }
            }
        }
        for (const method of s.calls ?? []) {
            const names =
                method === 'encodePartial'
                    ? (s.patches ?? [])
                    : method === 'keys' || method.startsWith('keyCondition')
                      ? (s.args ?? [])
                      : (s.items ?? [])
            if (method === 'keyConditionIndex') {
                for (const index of s.indexes ?? [])
                    for (const name of names) {
                        const vr = e.vars[name] as Var
                        const axes = {
                            value: vr.vk,
                            arg: name,
                            method: 'keyCondition',
                        }
                        const run = attempt(() =>
                            table.keyCondition(index, ev(vr.value) as object),
                        )
                        const text = `${T}.keyCondition(${index},${name})`
                        const c = call(
                            'keyCondition',
                            text,
                            `${T}.keyCondition('${index}', v_${e.id}_${name})`,
                            run,
                            axes,
                        )
                        if (run.ok)
                            result(
                                'keyCondition',
                                text,
                                c.v,
                                c.id,
                                run.value,
                                axes,
                            )
                    }
                continue
            }
            for (const name of names) {
                const vr = e.vars[name] as Var
                const axes = { value: vr.vk, arg: name, method }
                const value = ev(vr.value) as object
                const text = `${T}.${method}(${name})`
                if (method === 'fromItem') {
                    // the stored items: the item that toItem writes for the arg, and the empty item
                    const written = attempt(() => table.toItem(value))
                    const stored = written.ok ? [[name, written.value]] : []
                    for (const [label, item] of [...stored, ['empty', {}]] as [
                        string,
                        object,
                    ][]) {
                        const sv = `si_${hash}_${name}_${label}`
                        emit(`export const ${sv} = ${lit(item)} as const`)
                        const run = attempt(() => table.fromItem(item))
                        const t = `${T}.fromItem(${name},${label})`
                        const c = call(
                            'fromItem',
                            t,
                            `${T}.fromItem(${sv})`,
                            run,
                            axes,
                        )
                        if (run.ok)
                            result('fromItem', t, c.v, c.id, run.value, axes)
                    }
                    continue
                }
                const run = attempt(() =>
                    method === 'keys'
                        ? table.keys(value)
                        : method === 'keyCondition'
                          ? table.keyCondition(value)
                          : method === 'toItem'
                            ? table.toItem(value)
                            : table.codec.encodePartial(value),
                )
                const expr =
                    method === 'encodePartial'
                        ? `${T}.codec.encodePartial(v_${e.id}_${name})`
                        : `${T}.${method}(v_${e.id}_${name})`
                const c = call(method, text, expr, run, axes)
                if (run.ok) result(method, text, c.v, c.id, run.value, axes)
            }
        }
        for (const name of s.changes ?? []) {
            const vr = e.vars[name] as Var
            const axes = { value: vr.vk, arg: name, method: 'keyUpdates' }
            const run = attempt(() => table.keyUpdates(ev(vr.value) as object))
            const text = `${T}.keyUpdates(${name})`
            const c = call(
                'keyUpdates',
                text,
                `${T}.keyUpdates(v_${e.id}_${name})`,
                run,
                axes,
            )
            if (!run.ok) continue
            result('keyUpdates', text, c.v, c.id, run.value, axes)
            foreign(
                'keyUpdates',
                text,
                c.v,
                c.id,
                lit({ ...(run.value as object), remove: ['~'] }),
                axes,
                '',
            )
        }
    }
    return { files, rows, runs }
}

const tsconfig = (files: readonly string[]): string =>
    `${JSON.stringify(
        {
            extends: '../../tsconfig.json',
            compilerOptions: {
                rootDir: '../..',
                composite: false,
                declaration: false,
                declarationMap: false,
                noEmit: true,
                incremental: false,
                noUnusedLocals: false,
                noUnusedParameters: false,
            },
            files,
            include: [],
        },
        null,
        2,
    )}\n`

/** The files of the type directory: one program for the whole pool, and the rows of its checks. */
const entryFiles = (
    pool: ReturnType<typeof printPool>,
): readonly (readonly [string, string])[] => [
    ...pool.files.map((f, i) => [programFile(i), `${f.join('\n')}\n`] as const),
    [
        'rows.json',
        `${JSON.stringify(
            pool.rows.map(({ axes: _axes, run: _run, ...row }) => row),
            null,
            1,
        )}\n`,
    ],
    ...pool.files.map(
        (_f, i) =>
            [
                ['tsconfig.', programName(i), '.json'].join(''),
                tsconfig([programFile(i)]),
            ] as const,
    ),
]

let memo: ReturnType<typeof printPool> | undefined
const pool = () => {
    memo ??= printPool(1, false)
    return memo
}
const textOf = (row: Row) => row.id.split('|').slice(3).join('|')
const LONG = 120_000
const TYPING_ROWS = 65
const GROUP_ROWS = {
    typing: 65,
    constructAccept: 101,
    constructRefuse: 63,
    toEntry: 858,
    fromEntry: 681,
    infer: 524,
    key: 1113,
    keyUpdates: 87,
    keys: 12,
    keyCondition: 25,
    toItem: 6,
    fromItem: 12,
    encodePartial: 8,
}

describe('the pool of the entry methods', () => {
    it('reads a plain item as a text of one character or more with no separator, a number, or a boolean', () => {
        expect(plain({ petId: 'p1', n: 2, ok: true, owner: { id: 'o' } })).toBe(
            true,
        )
        expect(plain({ petId: '' })).toBe(false)
        expect(plain({ petId: 'a#b' })).toBe(false)
        expect(plain({ owner: null })).toBe(false)
        expect(plain({ owner: { id: '' } })).toBe(false)
    })

    it(
        'makes a construct row a refuse row where toEntry throws for a plain item, and an accept row where only another item throws',
        { timeout: LONG },
        () => {
            const construct = (text: string) =>
                pool().rows.find(
                    (r) => r.group === 'construct' && textOf(r) === text,
                )
            // owner is optional, the path can be absent, and the plain item with no owner throws
            expect(construct('opt.pathList')?.expect).toBe('refuse')
            // a path into a union of objects: the plain item of the option without the name throws
            expect(construct('doc.pathList')?.expect).toBe('refuse')
            // a name that no option of the arm holds: the plain item of the arm throws
            expect(construct('kind_single.nopath_spec_neg')?.expect).toBe(
                'refuse',
            )
            // the empty text and the text with the separator throw, and they are no plain item
            expect(construct('plain.list2')?.expect).toBe('accept')
            expect(construct('plain.listOne')?.expect).toBe('accept')
        },
    )

    it(
        'prints no method row for a table that a refuse row builds no entry for',
        { timeout: LONG },
        () => {
            const refused = pool()
                .rows.filter(
                    (r) => r.group === 'construct' && r.expect === 'refuse',
                )
                .map((r) => `T_${textOf(r).replace('.', '_')}.`)
            expect(refused.length).toBeGreaterThan(0)
            const methods = pool().rows.filter(
                (r) => !['construct', 'typing'].includes(r.group),
            )
            expect(
                methods.filter((r) =>
                    refused.some((t) => textOf(r).startsWith(t)),
                ),
            ).toEqual([])
        },
    )

    it(
        'gives each row one id, and no id depends on the order of the draws',
        { timeout: LONG },
        () => {
            const ids = pool().rows.map((r) => r.id)
            expect(new Set(ids).size).toBe(ids.length)
            const reversed = printPool(1, true).rows.map((r) => r.id)
            expect([...reversed].sort()).toEqual([...ids].sort())
        },
    )

    it(
        'puts each item of a draw to the entity type as a typing row that the bridge fails as a hard failure',
        { timeout: LONG },
        () => {
            const typing = pool().rows.filter((r) => r.group === 'typing')
            expect(
                typing.every(
                    (r) =>
                        r.expect === 'accept' &&
                        r.id.startsWith('typing|accept|'),
                ),
            ).toBe(true)
            expect(typing.length).toBe(TYPING_ROWS)
        },
    )

    it(
        'gives a foreign row only for a key text with a label, or for a key that a null arm does not write',
        { timeout: LONG },
        () => {
            const foreign = pool().rows.filter((r) =>
                textOf(r).includes('.foreign'),
            )
            // an attribute key holds any text, so it has no foreign value
            expect(
                foreign.filter(
                    (r) =>
                        /T_plain_attr(Name|Note)\./.test(textOf(r)) &&
                        (r.group === 'key' || textOf(r).endsWith(':SK')),
                ),
            ).toEqual([])
            expect(
                foreign.filter((r) => /T_union_null_none\./.test(textOf(r)))
                    .length,
            ).toBeGreaterThan(0)
            expect(
                foreign.filter((r) => /T_numname_numList\./.test(textOf(r)))
                    .length,
            ).toBeGreaterThan(0)
            // infer has no foreign row where another member of the union can hold any text at the key
            expect(
                foreign.filter(
                    (r) =>
                        r.group === 'infer' &&
                        /T_(top|union|literal|nested)_attr/.test(textOf(r)),
                ),
            ).toEqual([])
        },
    )

    it(
        'names the first row of the checks that a row reads in after, so the bridge reads one level',
        { timeout: LONG },
        () => {
            const byId = new Map(pool().rows.map((r) => [r.id, r]))
            for (const r of pool().rows) {
                if (r.group === 'construct' || r.group === 'typing') {
                    expect(r.after).toBeUndefined()
                    continue
                }
                expect(r.after?.length).toBeGreaterThan(0)
                expect(
                    byId.get((r.after as string[])[0] as string)?.group,
                ).toBe('construct')
            }
        },
    )

    it(
        'holds a match on a path where one option holds two literals at the path, with the items of each literal',
        { timeout: LONG },
        () => {
            const rows = pool().rows
            const table = 'kind_dpathdouble.nopath_spec_pos'
            expect(
                rows.find((r) => r.group === 'construct' && textOf(r) === table)
                    ?.expect,
            ).toBe('accept')
            const calls = rows
                .filter((r) => r.group === 'key')
                .map(textOf)
                .filter((t) =>
                    t.startsWith('T_kind_dpathdouble_nopath_spec_pos.'),
                )
            expect(calls).toEqual(
                expect.arrayContaining([
                    'T_kind_dpathdouble_nopath_spec_pos.key(SK,in,none).call',
                    'T_kind_dpathdouble_nopath_spec_pos.key(SK,out,none).call',
                    'T_kind_dpathdouble_nopath_spec_pos.key(SK,tag_in,none).call',
                    'T_kind_dpathdouble_nopath_spec_pos.key(SK,tag_out,none).call',
                ]),
            )
        },
    )

    it(
        'gives a toItem call that throws for a key component with no text a refuse row, as the owner ruled',
        { timeout: LONG },
        () => {
            const toItem = pool().rows.filter((r) => r.group === 'toItem')
            const verdict = (name: string) =>
                toItem.find(
                    (r) =>
                        textOf(r) === `T_plain_codecItem.toItem(${name}).call`,
                )?.expect
            expect(verdict('ok')).toBe('accept')
            expect(verdict('blank')).toBe('refuse')
            expect(verdict('sep')).toBe('refuse')
        },
    )

    it(
        'gives an error value of fromItem an accept call row, and the result row builds a CodecError',
        { timeout: LONG },
        () => {
            const rows = pool().rows
            const call = rows.find(
                (r) =>
                    textOf(r) === 'T_plain_codecItem.fromItem(ok,empty).call',
            )
            expect(call?.expect).toBe('accept')
            expect(
                rows.some(
                    (r) =>
                        textOf(r) ===
                        'T_plain_codecItem.fromItem(ok,empty).result',
                ),
            ).toBe(true)
            expect(pool().files[0]?.join('\n')).toContain('= new CodecError(')
        },
    )

    it(
        'draws the option separator for one table of each schema form that the type builds, and reads a label with that separator',
        { timeout: LONG },
        () => {
            const tables = new Set(
                pool()
                    .rows.filter((r) => r.group === 'construct')
                    .map(textOf)
                    .filter((t) => t.endsWith('_sep')),
            )
            expect([...tables].sort()).toEqual(
                [
                    'opt.pathList_sep',
                    'plain.attrNote_sep',
                    'plain.defaultFn_sep',
                    'plain.list2_sep',
                    'plain.tagTf_sep',
                    'opt.pathAttr_sep',
                    'opt.pathDefault_sep',
                    'kind_single.nopath_spec_pos_sep',
                    'kind_single.nopath_cases_pos_sep',
                    'kind_single.nullArms_sep',
                    'held.twoLevels_sep',
                ].sort(),
            )
            // a text with the label of the separator `|` has a foreign value, as a text with `#` has
            expect(pool().files[0]?.join('\n')).toContain('"~T|rex"')
        },
    )

    it(
        'draws keys and keyCondition with an argument that holds no component of the key, or a prefix of it',
        { timeout: LONG },
        () => {
            const verdict = (text: string) =>
                pool().rows.find((r) => textOf(r) === text)?.expect
            expect(verdict('T_plain_roleKeys.keys(ok).call')).toBe('accept')
            expect(verdict('T_plain_roleKeys.keys(none).call')).toBe('refuse')
            expect(verdict('T_plain_roleKeys.keys(pidOnly).call')).toBe(
                'refuse',
            )
            expect(verdict('T_plain_roleKeys.keyCondition(pidOnly).call')).toBe(
                'accept',
            )
            expect(verdict('T_plain_indexKeys.keyCondition(G1,ok).call')).toBe(
                'accept',
            )
            expect(
                verdict('T_plain_indexKeys.keyCondition(G1,none).call'),
            ).toBe('refuse')
        },
    )

    it(
        'states the argument variable as the site of a call row, because a refused call starts its error at the argument',
        { timeout: LONG },
        () => {
            const at = (text: string) =>
                pool().rows.find((r) => textOf(r) === text)?.at
            expect(at('T_plain_roleKeys.keys(none).call')).toBe('v_plain_none')
            expect(at('T_plain_list2.toEntry(blank).call')).toBe(
                'v_plain_blank',
            )
            expect(at('T_plain_list2.key(SK,blank,none).call')).toBe(
                'v_plain_blank',
            )
            // every call row states a site, and the other groups state none
            const calls = pool().rows.filter((r) => textOf(r).endsWith('.call'))
            expect(calls.every((r) => r.at !== undefined)).toBe(true)
            expect(
                pool()
                    .rows.filter(
                        (r) =>
                            r.at !== undefined && !textOf(r).endsWith('.call'),
                    )
                    .every(
                        (r) =>
                            /foreign:|^construct$/.test(textOf(r)) ||
                            r.group === 'construct',
                    ),
            ).toBe(true)
        },
    )

    it(
        'states the property as the site of a foreign property row, and no site for the foreign result of key or keyUpdates',
        { timeout: LONG },
        () => {
            const rows = pool().rows
            const at = (text: string) =>
                rows.find((r) => textOf(r) === text)?.at
            expect(at('T_plain_list2.toEntry(ok).foreign:SK')).toBe('"SK"')
            expect(at('T_plain_list2.infer(ok).foreign:SK')).toBe('"SK"')
            const results = rows.filter(
                (r) =>
                    (r.group === 'key' || r.group === 'keyUpdates') &&
                    textOf(r).endsWith('.foreign'),
            )
            expect(results.length).toBeGreaterThan(0)
            // the compiler puts the error on the declared name of `const r: T = "text"`: a site there tests the row
            expect(results.filter((r) => r.at !== undefined)).toEqual([])
        },
    )

    it(
        'declares the site and the rule for the negative pole of a kind, and none for the positive pole',
        { timeout: LONG },
        () => {
            const construct = (text: string) =>
                pool().rows.find(
                    (r) => r.group === 'construct' && textOf(r) === text,
                )
            const neg = construct('kind_single.nopath_cases_neg')
            expect(neg?.at).toBe("'ownerId'")
            expect(neg?.rule).toBe('is no name or path of the entity')
            const pos = construct('kind_single.nopath_cases_pos')
            expect(pos?.at).toBeUndefined()
            expect(pos?.rule).toBeUndefined()
            // a draw that names no element states no site
            expect(construct('opt.pathList')?.at).toBeUndefined()
        },
    )

    it(
        'declares the discriminator and the rule that it can be absent, for the kinds that can lack a discriminator, in the negative pole and in the cases form',
        { timeout: LONG },
        () => {
            const construct = (text: string) =>
                pool().rows.find(
                    (r) => r.group === 'construct' && textOf(r) === text,
                )
            for (const kind of ['kind_optional', 'kind_lacking']) {
                for (const table of [
                    `${kind}.nopath_spec_neg`,
                    `${kind}.nopath_cases_neg`,
                    `${kind}.nopath_cases_pos`,
                ]) {
                    expect(construct(table)?.at).toBe("discriminator: 'kind'")
                    expect(construct(table)?.rule).toBe('can be absent')
                }
                // the spec form of the positive pole lands on an arm name, with the rule of another refusal
                expect(construct(`${kind}.nopath_spec_pos`)?.at).toBeUndefined()
            }
            expect(construct('kind_single.nopath_cases_neg')?.at).toBe(
                "'ownerId'",
            )
        },
    )

    it('pins the count of the rows of each group', { timeout: LONG }, () => {
        const count = (g: string, v?: string) =>
            pool().rows.filter(
                (r) => r.group === g && (v === undefined || r.expect === v),
            ).length
        expect({
            typing: count('typing'),
            constructAccept: count('construct', 'accept'),
            constructRefuse: count('construct', 'refuse'),
            toEntry: count('toEntry'),
            fromEntry: count('fromEntry'),
            infer: count('infer'),
            key: count('key'),
            keyUpdates: count('keyUpdates'),
            keys: count('keys'),
            keyCondition: count('keyCondition'),
            toItem: count('toItem'),
            fromItem: count('fromItem'),
            encodePartial: count('encodePartial'),
        }).toEqual(GROUP_ROWS)
    })

    it(
        'emits the type vectors of the entry methods for the gate',
        { timeout: LONG },
        () => {
            const files = entryFiles(pool())
            if (process.env.EMIT_LEAN_REFUSALS) {
                const types = join(process.cwd(), 'formal', '.entry.types')
                mkdirSync(types, { recursive: true })
                for (const [file, text] of files)
                    writeFileSync(join(types, file), text)
            }
            expect(files.map(([file]) => file)).toEqual([
                'entries0.ts',
                'rows.json',
                'tsconfig.entries0.json',
            ])
        },
    )
})
