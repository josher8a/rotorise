import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    every,
    exclude,
    extract,
    fill,
    held,
    legacy,
    list,
    mdunion,
    meet,
    narrow,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    ref,
    refine,
    scope,
    spread,
    string,
    tableEntry,
    undefinable,
    union,
    item,
    at,
    path,
    pathBuilder,
    pin,
    preconditions,
} from 'rotorise'
import * as R from 'rotorise'
import {
    arbitraryOf,
    checkAgainst,
    checkDecodesAreWritable,
    checkEncodePaths,
    checkEquivalent,
    checkIso,
    checkMembersStable,
    checkRoundTrip,
    checkStable,
    firstDifference,
    rngFrom,
    roundTrip,
    shrinkOf,
    structuralEquals,
} from 'rotorise/testing'
import { native } from 'rotorise/native'

// A consumer exports the result of each call below with `declaration: true`. The declaration
// emitter names each type that the declaration prints, and the entry publishes each such name.
// A constant that the emitter cannot name is a type that the entry must publish. A marker key that
// the declaration prints in place is a string literal, because the emitter cannot write a symbol key.
// A type that contains itself has a name, because the emitter writes `any` for a cycle with no name.

const Dog = object({ kind: string('DOG'), name: string, age: optional(number) })
const Cat = object({ kind: string('CAT'), name: string, lives: number })
const Pet = union([Dog, Cat])
export { Dog, Cat, Pet }

export const Named = refine(string, (s: string): s is string => s.length > 0)
export const Count = held(string, number, { encode: (n: number) => String(n), decode: (t: string) => Number(t) })
export const Tags = array(string)
export const DogName = at(item(Dog), ['name'])
export const DogItem = item(Dog)
export const PetItem = item(Pet)
export const OnlyDogRow = narrow(at(item(Pet), []), object({ kind: string('DOG') }))
type PetRow = { petId: string; kind: 'DOG'; ownerId: string } | { petId: string; kind: 'CAT' }
export const PetRows = tableEntry<PetRow>()({
    PK: ['petId'],
    SK: { discriminator: 'kind', spec: { DOG: ['ownerId'], CAT: null } },
})
export const Packs = scope({
    Pet: union([
        object({ kind: string('DOG'), mate: optional(ref('Pet')) }),
        object({ kind: string('CAT'), lives: number }),
    ]),
})
export const { Pet: PackPet } = Packs
export const Families = scope({ Family: object({ name: string, children: optional(array(ref('Family'))) }) })
export const { Family } = Families
export const CodedPets = tableEntry<{ petId: string; name: string }>()(
    { PK: ['petId'], GSI1SK: 'name' },
    { codec: { petId: string, name: string }, key: { partition: 'PK' } },
)
export const TaggedPets = tableEntry<PetRow>()(
    { PK: ['petId'], SK: { discriminator: 'kind', spec: { DOG: ['ownerId'], CAT: null } } },
    {
        codec: item(
            discriminatedUnion('kind', [
                object({ petId: string, kind: string('DOG'), ownerId: string }),
                object({ petId: string, kind: string('CAT') }),
            ]),
        ),
    },
)
export const Chip = binary
export const Vaccinated = boolean
export const Carry = R.carrying
export const CE = R.CodecError
export const Price = decimal
export const Tagged = discriminatedUnion('kind', [Dog, Cat])
export const DN = R.DynamoNumber
export const Every = every
export const EveryEntry = R.everyEntry
export const NotDogs = exclude(Pet, object({ kind: string('DOG') }))
export const Dogs = extract(Pet, object({ kind: string('DOG') }))
export const Failed = R.failed
export const Filled = object({ a: fill(string, 'x') })
export const CountAgain = held(string, number, { encode: (n: number) => String(n), decode: (t: string) => Number(t) })
export const IN = R.isNumeral
export const KC = R.keyComponents
export const Old = legacy({ current: object({ name: string }), older: object({ name: string }) })
export const Route = list(string, number)
export const Multi = mdunion(['kind'], [Dog, Cat])
export const Both = meet(object({ name: string }), object({ age: number }))
export const Member = R.memberOf
export const Nope = never
export const Nick = nullable(string)
export const Nothing = nullValue
export const Age = number
export const Lives = number(9)
export const AgeSet = number.set()
export const Owner = object({ name: string, tags: array(string) })
export const Counts = object({ kind: string('DOG') }, [string, optional(string)])
export const Any = opaque
export const Opt = object({ a: optional(string) })
export const OrThrow = R.orThrow
export const DogPath = path(at(item(Dog), ['name']))
export const Paths = pathBuilder<{ name: string }>()
export const Pinned = pin<{ name: string }>()(object({ name: string }))
export const Pre = preconditions(at(item(Dog), ['name']))
export const Next = ref('X')
export const NamedAgain = refine(string, (s: string): s is string => s.length > 0)
export const TagSet = string.set()
export const Shape = R.shapeOf
export const OnlyDog = extract(Pet, object({ kind: string('DOG'), name: string }))
export const Weights = list(string, spread(number))
export const Name = string
export const Kind = string('DOG')
export const Kinds = string('DOG', 'CAT')
export const TD = R.tooDeeplyNested
export const Und = object({ a: undefinable(string) })
export const Animal = union([Dog, Cat])
export const rng = rngFrom(1)
export const sample = arbitraryOf(object({ name: string }), rng, 3)
export const roundTripped = roundTrip
export const checked = checkRoundTrip
export const difference = firstDifference
export const Marshal = native({ removeUndefinedValues: true })
export const Bare = native
const Shelter = scope({ Pet: union([object({ kind: string('DOG'), name: string }), object({ kind: string('CAT'), lives: number })]) })
export const ScopedDogs = extract(Shelter.Pet, object({ kind: string('DOG') }))
export const ScopedNotDogs = exclude(Shelter.Pet, object({ kind: string('DOG') }))
export const MaxNesting = R.MAX_DOCUMENT_NESTING
export const Refusal = R.RotoriseError
export const Then = R.andThen
export const StoredNumeral = R.isStoredNumeral
export const against = checkAgainst
export const writable = checkDecodesAreWritable
export const encodePaths = checkEncodePaths
export const equivalent = checkEquivalent
export const iso = checkIso
export const membersStable = checkMembersStable
export const stable = checkStable
export const shrink = shrinkOf
export const structural = structuralEquals
// Not in this project: a cycle that goes through a list and a union only has no name for the decoded
// type of the union, so the declaration holds `any` and TypeScript 7 refuses it (TS5088):
//   scope({ Nest: array(ref('Tags')), Tags: union([string('PUPPY'), ref('Nest')]) })
