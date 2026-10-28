/**
 * A read checks each derived key, and a key build refuses a segment that holds the separator.
 *
 * A key is the join of its segments. Two lists of segments give one key where a segment holds the
 * separator, so a key with such a segment reads back as another list. The build refuses the segment
 * and names the component. A stored key that differs from the key that the attributes build is a row
 * that another writer wrote, and the read refuses it and names the key. A key that the row lacks
 * only says that the row is not in that index.
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
    it('refuses a key that disagrees with its attributes, and names the key', () => {
        const entry = { ...Users.toEntry(user), GSI1SK: 'EMAIL#other@b.c' }
        const out = read(entry)
        expect(failed(out)).toBe(true)
        expect(out).toBeInstanceOf(CodecError)
        expect((out as CodecError).path).toEqual(['GSI1SK'])
        expect((out as CodecError).message).toContain('GSI1SK')
        expect((out as CodecError).message).not.toContain('other@b.c')
    })

    it('accepts a row that lacks a key attribute', () => {
        const { GSI1PK: _a, GSI1SK: _b, ...row } = Users.toEntry(user)
        expect(read(row)).toEqual(user)
    })

    it('refuses a key that its attributes cannot build', () => {
        const { email: _gone, ...row } = Users.toEntry(user)
        const out = read(row)
        expect(failed(out)).toBe(true)
        expect((out as CodecError).path).toEqual(['GSI1SK'])
    })

    it('gives the item for a row that toEntry wrote', () => {
        expect(read(Users.toEntry(user))).toEqual(user)
    })
})

describe('a read of a stored item', () => {
    const item = Users.toItem(user)

    it('refuses a key that disagrees with its attributes, and names the key', () => {
        if (failed(item)) throw item
        const out = Users.fromItem({ ...item, SK: { S: 'ROLE#other' } })
        expect(failed(out)).toBe(true)
        expect((out as CodecError).path).toEqual(['SK'])
        expect((out as CodecError).message).not.toContain('other')
    })

    it('accepts a row that lacks a key attribute', () => {
        if (failed(item)) throw item
        const { GSI1PK: _a, GSI1SK: _b, ...row } = item
        expect(Users.fromItem(row)).toEqual(user)
    })

    it('gives the item for a row that toItem wrote', () => {
        if (failed(item)) throw item
        expect(Users.fromItem(item)).toEqual(user)
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
