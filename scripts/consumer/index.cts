import {
    array,
    type Attribute,
    type AttributeValue,
    boolean,
    type Decoded,
    discriminatedUnion,
    type Encoded,
    exclude,
    extract,
    item,
    type ItemCodec,
    list,
    number,
    type NumberCodec,
    object,
    optional,
    ref,
    type Result,
    scope,
    string,
    type StringCodec,
    tableEntry,
    union,
} from 'rotorise'
import { arbitraryOf, checkRoundTrip, rngFrom } from 'rotorise/testing'
import { native } from 'rotorise/native'

type Pet =
    | { petId: string; kind: 'DOG'; ownerId: string }
    | { petId: string; kind: 'CAT' }

export const Pets = tableEntry<Pet>()({
    PK: ['petId'],
    SK: {
        discriminator: 'kind',
        spec: { DOG: ['ownerId'], CAT: null },
    },
})

export const Dog = object({ kind: string('DOG'), name: string, age: optional(number) })
export const Cat = object({ kind: string('CAT'), name: string, lives: number })
export const Animal = union([Dog, Cat])
export const Tagged = discriminatedUnion('kind', [Dog, Cat])
export const Dogs = extract(Animal, object({ kind: string('DOG') }))
export const NotDogs = exclude(Animal, object({ kind: string('DOG') }))
export const { Tree } = scope({
    Tree: object({ name: string, children: optional(array(ref('Tree'))) }),
})
export const Litters = object({ litter: list(string, number), vaccinated: boolean })

export type AnimalValue = Decoded<typeof Animal>
export type AnimalStored = Encoded<typeof Animal>
export const dog: Decoded<typeof Dogs> = { kind: 'DOG', name: 'Rex' }
export const stored = Dogs.unsafeEncode(dog)
export const cat: Decoded<typeof NotDogs> = { kind: 'CAT', name: 'Tom', lives: 9 }
export const sample: Decoded<typeof Tree> = { name: 'pets', children: [{ name: 'dogs' }] }
export const marshalled = native({ removeUndefinedValues: true })
export const roundTrip = checkRoundTrip(item(Dog))
export const generated = arbitraryOf(Animal, rngFrom(1), 3)

// A call that the types refuse, inside a thunk that a function takes: the shape of `expect(() => ...)`.
// The refusal must reach the end of the walk of the key on every compiler.
declare const expectThrow: <T>(actual: T) => { toThrow: () => void }
export const refused = expectThrow(() =>
    tableEntry<Pet>()(
        { PK: ['petId'] },
        // @ts-expect-error an empty separator joins no segments apart
        { separator: '' },
    ),
).toThrow()

// A pin holds when the result and the pin are one type. Assignability in two directions is not enough:
// `any` inside a member is assignable both ways, and so is an intersection against the one object that
// it merges to. The pin states the pin as a type argument, and the rest parameter refuses the call where
// the two types are not identical. The test is the identity that the compiler uses for two
// conditional types, which each compiler resolves alike.
type Unequal<Pinned, Result> = (<T>() => T extends Pinned ? 1 : 2) extends <
    T,
>() => T extends Result ? 1 : 2
    ? []
    : ['the result is not the pin']
declare const pinned: <Pinned>() => <Result>(
    result: Result,
    ...unequal: Unequal<Pinned, Result>
) => Result

// The floor of a pin. A pin names no type of rotorise for the part that it measures, because the identity
// resolves an alias before it compares, and a mutant of the alias then keeps the pin green. So a pin states
// the structure down to the floor, and the floor is: `Attribute` and `AttributeValue` (one value of DynamoDB),
// `Result`, the codec classes (`ItemCodec`, `StringCodec`, `NumberCodec`), and the primitive types.
type Member = Attribute<'S'> | Attribute<'N'> | Attribute<'B'>
type Values = { readonly [name: string]: AttributeValue }
type Sort<Name extends string> =
    | { readonly name: Name; readonly equals: Member }
    | { readonly name: Name; readonly beginsWith: Attribute<'S'> }

// The methods of an entry with a codec. One record holds one pin for each key of the entry, so a method
// that a later pass adds with no pin is an error here: `satisfies` asks for each key of `Kennels`. A method
// with more than one form holds one pin for each form.
type Kennel = { petId: string; shelterId: string; name: string; age: number }
export const Kennels = tableEntry<Kennel>()(
    { PK: ['petId'], SK: ['name'], GSI1PK: 'shelterId', GSI1SK: ['age'] },
    {
        codec: { petId: string, shelterId: string, name: string, age: number },
        key: { partition: 'PK', sort: 'SK' },
        indexes: { GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' } },
    },
)
const kennel: Kennel = { petId: 'p1', shelterId: 's1', name: 'Rex', age: 3 }
const ids = { petId: 'p1' } as const
const shelter = { shelterId: 's1' } as const
const older = { age: 4 } as const
type KennelEntry = {
    petId: string
    shelterId: string
    name: string
    age: number
    readonly PK: `PETID#${string}`
    readonly SK: `NAME#${string}`
    readonly GSI1PK: string
    readonly GSI1SK: `AGE#${number}`
}
type KennelRow = {
    readonly petId: Attribute<'S'>
    readonly shelterId: Attribute<'S'>
    readonly name: Attribute<'S'>
    readonly age: Attribute<'N'>
    readonly PK: Attribute<'S'>
    readonly SK: Attribute<'S'>
    readonly GSI1PK: Attribute<'S'>
    readonly GSI1SK: Attribute<'S'>
}
const storedKennel = {
    petId: { S: 'p1' },
    shelterId: { S: 's1' },
    name: { S: 'Rex' },
    age: { N: '3' },
} as const
export const kennelPins = {
    toEntry: pinned<KennelEntry>()(Kennels.toEntry(kennel)),
    fromEntry: pinned<Kennel>()(Kennels.fromEntry(Kennels.toEntry(kennel))),
    key: {
        plain: pinned<'PETID#p1'>()(Kennels.key('PK', ids)),
        ofOne: pinned<'s1'>()(Kennels.key('GSI1PK', shelter)),
        ofEntity: pinned<`NAME#${string}`>()(Kennels.key('SK', kennel)),
        depth: pinned<`NAME#${string}`>()(Kennels.key('SK', kennel, { depth: 1 })),
        partial: pinned<'' | `NAME#${string}`>()(
            Kennels.key('SK', kennel, { allowPartial: true }),
        ),
        boundary: pinned<'' | `NAME#${string}`>()(
            Kennels.key('SK', kennel, { allowPartial: true, enforceBoundary: true }),
        ),
    },
    keyUpdates: pinned<{ set: Values; remove: readonly 'GSI1PK'[] }>()(
        Kennels.keyUpdates(older),
    ),
    keys: {
        names: pinned<Values>()(Kennels.keys(['PK', 'SK'], kennel)),
        attributes: pinned<Values>()(Kennels.keys(kennel)),
    },
    keyCondition: {
        attributes: pinned<{
            readonly partition: { readonly name: 'PK'; readonly value: Member }
            readonly sort?: Sort<'SK'>
        }>()(Kennels.keyCondition(ids)),
        index: pinned<{
            readonly index: 'GSI1'
            readonly partition: { readonly name: 'GSI1PK'; readonly value: Member }
            readonly sort?: Sort<'GSI1SK'>
        }>()(Kennels.keyCondition('GSI1', shelter)),
    },
    infer: pinned<KennelEntry>()(Kennels.infer),
    path: [
        pinned<string>()(Kennels.path().name.toString()),
        // @ts-expect-error the entity holds no attribute `nope`, so the path refuses the name
        Kennels.path().nope,
    ],
    toItem: pinned<Result<KennelRow>>()(Kennels.toItem(kennel)),
    unsafeToItem: pinned<KennelRow>()(Kennels.unsafeToItem(kennel)),
    fromItem: pinned<Result<Kennel>>()(Kennels.fromItem(storedKennel)),
    unsafeFromItem: pinned<Kennel>()(Kennels.unsafeFromItem(storedKennel)),
    codec: pinned<
        ItemCodec<
            Kennel,
            {
                readonly petId: StringCodec
                readonly shelterId: StringCodec
                readonly name: StringCodec
                readonly age: NumberCodec
            }
        >
    >()(Kennels.codec),
} satisfies { [K in keyof typeof Kennels]: unknown }

// The entry of a union, with a match key: an arm that names no key gives no key.
const pet: Pet = { petId: 'p1', kind: 'CAT' }
const dogPet = { petId: 'p1', kind: 'DOG', ownerId: 'o1' } as const
const catPet = { petId: 'p1', kind: 'CAT' } as const
export const petPins = {
    // the arm `CAT: null` builds no value, so the row holds no `SK`, and the type holds `SK` as optional
    entryOfUnion: (value: Pet) =>
        pinned<
            | {
                  readonly PK: `PETID#${string}`
                  readonly SK: `OWNERID#${string}`
                  petId: string
                  kind: 'DOG'
                  ownerId: string
              }
            | {
                  readonly PK: `PETID#${string}`
                  readonly SK?: never
                  petId: string
                  kind: 'CAT'
              }
        >()(Pets.toEntry(value)),
    key: pinned<'PETID#p1'>()(Pets.key('PK', { petId: 'p1' })),
    keyOfEntity: pinned<`PETID#${string}`>()(Pets.key('PK', pet)),
    keyOfDog: pinned<'OWNERID#o1'>()(Pets.key('SK', dogPet)),
    keyOfCat: pinned<undefined>()(Pets.key('SK', catPet)),
    keyUpdates: pinned<{ set: Values; remove: readonly 'SK'[] }>()(
        Pets.keyUpdates({ kind: 'DOG', ownerId: 'o2' }),
    ),
}
