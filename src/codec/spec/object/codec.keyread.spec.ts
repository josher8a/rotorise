/**
 * A read never reads a derived key, and a key build refuses a segment that holds the separator.
 *
 * A key is the join of its segments. Two lists of segments give one key where a segment holds the
 * separator, so a key with such a segment reads back as another list. The build refuses the segment
 * and names the component, so that two items never share one key. The key adds no information to the
 * attributes, so a row with a correct key, a stale key or no key decodes to one item.
 */
import { describe, expect, it } from 'vitest'
import {
    CodecError,
    failed,
    RotoriseError,
    tableEntry,
} from '../../../Rotorise'
import { string } from '../../codec'

type User = { orgId: string; id: string; role: string; email: string }

const Users = tableEntry<User>()(
    { PK: ['orgId', 'id'], SK: ['role'], GSI1PK: ['role'], GSI1SK: ['email'] },
    { codec: { orgId: string, id: string, role: string, email: string } },
)

const user: User = { orgId: 'acme', id: '1', role: 'admin', email: 'a@b.c' }

/** The untyped read of an entry: a stored row is data that another writer wrote. */
const read = Users.fromEntry as (entry: object) => unknown

describe('a read of an entry', () => {
    const entry = Users.toEntry(user)
    const { GSI1PK: _a, GSI1SK: _b, ...absent } = entry
    const { email: _gone, ...unbuildable } = entry
    const stale = { ...entry, GSI1SK: 'EMAIL#other@b.c' }

    it('gives one item for a row with a correct key, a stale key, or an absent key', () => {
        for (const [name, row] of Object.entries({ entry, stale, absent })) {
            expect(read(row), name).toEqual(user)
        }
    })

    it('returns no failure for a row that lacks an attribute that a key reads', () => {
        const out = read(unbuildable)
        expect(failed(out)).toBe(false)
        expect(out).not.toBeInstanceOf(CodecError)
    })
})

describe('a read of a stored item', () => {
    const item = Users.toItem(user)

    it('gives one item for a row with a correct key, a stale key, or an absent key', () => {
        if (failed(item)) throw item
        const { GSI1PK: _a, GSI1SK: _b, ...absent } = item
        const rows = {
            correct: item,
            stale: { ...item, SK: { S: 'ROLE#other' } },
            absent,
        }
        for (const [name, row] of Object.entries(rows)) {
            expect(Users.fromItem(row), name).toEqual(user)
        }
    })

    it('still fails where the attributes do not decode, and names no key', () => {
        if (failed(item)) throw item
        const { email: _gone, ...row } = item
        const out = Users.fromItem(row)
        expect(failed(out)).toBe(true)
        expect((out as CodecError).path).not.toContain('GSI1SK')
    })
})

describe('a key build', () => {
    it('refuses a value that holds the separator, and the message holds no value', () => {
        const bad = { ...user, orgId: 'a#secret' }
        const build = () => Users.key('PK', bad)
        expect(build).toThrow(RotoriseError)
        expect(build).toThrow(/orgId/)
        expect(build).not.toThrow(/secret/)
        expect(() => Users.toEntry(bad)).toThrow(RotoriseError)
    })

    it('refuses a transform whose tag holds the separator', () => {
        const Tagged = tableEntry<User>()({
            PK: [['orgId', (x: string) => ({ tag: 'T#X', value: x })]],
        })
        const build = () => Tagged.key('PK', { orgId: 'acme' })
        expect(build).toThrow(RotoriseError)
        expect(build).toThrow(/tag of orgId/)
        expect(build).not.toThrow(/acme/)
    })

    it('refuses a transform whose value holds the separator', () => {
        const Prefixed = tableEntry<User>()({
            PK: [['orgId', (x: string) => `ORG#${x}`]],
        })
        expect(() => Prefixed.key('PK', { orgId: 'acme' })).toThrow(/orgId/)
    })

    it('builds the key of a value that holds a part of a longer separator', () => {
        const Dashed = tableEntry<User>()({ PK: ['orgId'] }, '::')
        expect(Dashed.key('PK', { orgId: 'a:b' })).toBe('ORGID::a:b')
        expect(() => Dashed.key('PK', { orgId: 'a::b' })).toThrow(/orgId/)
    })

    it('does not read a component that a depth cuts off', () => {
        expect(Users.key('PK', { ...user, id: 'a#b' }, { depth: 1 })).toBe(
            'ORGID#acme',
        )
    })
})
