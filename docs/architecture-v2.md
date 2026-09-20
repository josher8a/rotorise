# Architecture of the Lean development, version 2

**THIS DOCUMENT DOES NOT GOVERN YET.** `docs/architecture.md` is the normative description of
the system as it stands. This file describes the system the arc is building toward. Where the
two disagree, `architecture.md` is right about today and this file is right about the intent.

Read this before proposing a change to the term language, so that a pass moves toward the target
rather than away from it.

## How this file stops being a draft

Three things happen together, and none of them is a judgment call.

1. The structure below exists under `Calculus/`.
2. This file replaces `docs/architecture.md`, under that name.
3. `formal/scripts/name_drift.py` swaps the two in its `CURRENT` list.

Point 3 is the one that matters and the reason the other two are written down. **This file is
not name-checked today**, because every guarded document is in that list and this one is not.
A guarded document cannot cite a declaration that does not exist, and this file cites several on
purpose. So it carries the risk that every unguarded document carries: a name here can go stale
and nothing reports it. Treat a name in this file as a proposal, and the tree as the authority.

This file carries no count, no line number and no measurement, for the reason
`architecture.md` gives. The measurements that produced this design, the probes that tested it,
and the decisions still open are in the repository memory, not here. A reader who needs the
evidence reads that. A reader who needs the intent reads this.

| For | Read |
| --- | --- |
| The system as it stands, normatively | `docs/architecture.md` |
| The rules, normatively | `formal/docs/blueprint/src/content.tex` |
| Future states, and what decides each | `docs/roadmap.md` |
| Known, suspected and partially mitigated issues | `docs/defects.md` |
| The evidence, the probes and the open decisions | the repository memory |

---

## 1. The one question, asked twice

A term denotes a codec: a partial write from a value to an attribute, and a partial read back.
A union holds options, and the calculus decides at declaration time whether the options can be
told apart, because selection must find at most one option claiming a given thing.

"Told apart" is two questions.

    no value is written by two options
    no attribute is read by two options

A pair disjoint on one side alone is not disjoint. Two terms can write different value kinds and
store at the same member, and then encoding is unambiguous while decoding is not.

So every operation here answers one shape of question: **is the intersection of two described
sets empty?**

## 2. Where the certificate lives, and why it has no choice

The calculus cannot read the concrete sets. A value set is infinite, a predicate is a host
function, an adapter is a caller's function. So it decides in an **abstract domain**: a finite
description of each set, with a meet and a decidable test for the bottom.

The soundness obligation runs one way, from the concrete set into the description. The
consequence the calculus relies on is the standard one: **disjointness proved in the abstract
domain transfers to the concrete domain.** It does not transfer upward. Two concrete sets can be
disjoint while their descriptions overlap, and that is what an abstraction is rather than a
defect of one.

**Therefore the exact term meet is not the certificate.** The meet is exact concretely: it
admits what both factors admit, and that law is worth keeping. A certificate built on it reports
two options disjoint while the descriptions the runtime reads still overlap, and the runtime
then finds two claimants for one thing.

The abstract domain needs its own meet. That single fact is what the rest of this file follows
from.

**The boundary is a constructor, not a judgment.** At an option that is not an object, the
structural test *is* the concrete row, so the term meet decides correctly there. At an object the
two differ, and the abstract meet has real work only there.

### The lattice is complete and the term language is not

The term language has a bottom and no top. No term admits every value, because a term denotes a
codec and no codec encodes every value.

The description has a top and needs one: occupancy has it, and the value side of an uncertified
adapter is it. So **the top belongs to the description and not to the term language**, and the
asymmetry is forced rather than missing. A host constructs the top's **projection**, never the
top: the opaque term is that projection, and its flag says whether the projection loses.

## 3. What the structure demands of any description

**D1. A description is total over its index.** A description answering only at declared names is
a partial function pretending to be total, and every reader then carries the undeclared case by
hand. The undeclared case is a value of the description: an open block claims every name, a
closed body refuses every name it does not declare.

**D2. A description of a sum is a sum.** A name admits absence, or presence carrying a value.
Storing that as two independent fields and meeting them separately meets a product, and a
product meet fires only where one coordinate alone is empty. A pair separated by the two
coordinates together is missed.

**D3. A restriction has a carrier.** A restriction with no carrier describes a set no term
describes, so the abstraction has nothing to abstract, and only the top can approximate it.

**D4. A projection keeps what the decision reads.** A description that drops a fact the
certificate needs is blind by construction, and no proof recovers it. A projection is part of the
abstraction and owes the same soundness as the rest.

**D5. Analysability is a field, and the field is whether the premises are discharged.** An
arbitrary host predicate forces the description to the top there, and that is forced: keeping
discriminating power over an arbitrary predicate needs a solver over a restricted logic or a
syntactic reading of control flow, and neither survives a kernel decision procedure.

The cut is not data against function, because the system ships functions and knows what they do.
It is not the system's against the caller's either, because that is privilege rather than
structure. **It is whether the premises are discharged, and certification is open.** A caller
who discharges the laws earns what the library earns.

**D6. The description decides in the kernel.** Every test the certificate runs computes, and no
route reaches a classical axiom. Equality on a finite index is available; equality on a finite
set of them is not.

**D7. A concept lives outside the language exactly when it is terminal in it.** If no constructor
position accepts a concept, moving it outside removes a row from every table and closes off
nothing reachable. If any position accepts it, moving it outside makes a reachable state
unwritable, and encoding exists to do the opposite. The alternate reader is terminal and sits
outside. An adapter is a union option and composes with itself, so it is a constructor.

---

## 4. The term language

### A carrier and a restriction, and an adapter beside them

A literal and a refinement both restrict what a carrier accepts, differing only in the size of
the set. **A set of admissible values is one concept and a literal is its singleton.** So the
alternatives a name is pinned to and the members a refinement admits are one type, and the
disjointness test over them is one function rather than a general one beside a hand-written
special case.

An adapter does not restrict. It **re-indexes**, which is why it commutes with nothing: a
refinement outside an adapter tests the caller's value and the same refinement inside tests the
carrier's. Those are different facts and both are wanted, so the two orders are not collapsed.

    Restriction      a predicate on one value: commutative, idempotent, a meet
    an adapter       a change of coordinates: associative, non-commutative, a composition

Restrictions compose, because an adapter needs a second restriction naming the values it owns.

### The alternating stack

A term is a carrier with layers around it. Adjacent layers of one kind collapse: restrictions
conjoin, adapters compose. A mixed pair does not, and the term is carried as written.

The description does not collapse it either. **The value side of a description lives at the
caller's level**, so the rule is positional: read every restriction outside the outermost
adapter directly, and take the top from the outermost adapter inward. Nothing crosses an
adapter, so nothing is transported, so no property of an adapter's function is ever required.

The stored side needs no rule. An adapter is transparent there, so the description reads through
the whole stack to the carrier.

### An adapter's domain

A host type is erased before the certificate's question is asked. So a distinction living only
in the host's types buys nothing, and an adapter's value domain falls in three cases: one the
runtime can test, two brands over one carrier that it cannot, and a brand against its own
carrier which is not disjoint at all.

**Which values an adapter owns is a restriction on values, so it is an operand and not an
obligation.** An adapter carrying a domain test is two restrictions composed, and its value side
stops being the top. Where no test is given the top is correct, and **the refusal is the product
working** rather than a gap in it.

### A name description is an admissible set

A name admits absence, or presence carrying a value. That is one set and one emptiness test, not
two coordinates tested in two phases with a presence equality guarding the second. The guard is
the absent summand, and writing it by hand in the other phase is what makes a pair separated by
the two summands together go unseen.

The description also carries the stored signature of a field. Without it, two objects declaring
one name at two different types describe identically, and the object phase is blind by
construction.

---

## 5. What is host-relative, and what is not

**The value universe is the host's, and the core currently fixes one.** It names an opaque
numeric type concretely and carries no decimal carrier, so a decimal value is a text value.
Those are host facts, not laws: a host with an arbitrary-precision primitive separates them.

Everything derived from that collapse is therefore a property of a chosen universe. The text
base and the decimal base sharing a value slot while storing at different members is one such
thing, and so is every refusal that follows from it.

**The core already knows how to state premises instead of fixing an instance.** The numeric host
is a structure over any carrier, with a spelling, a reader, a round trip and a decidable
equality, and it has inhabitants that need no opaque type at all. That is the pattern: the core
states what a host must provide, the host provides it, and the term references it.

**A base of the language is an adapter.** The platform-number base and the host-independent
decimal base have the adapter's signature exactly: the stored side passes through and the value
side is re-indexed, with the round trip proved rather than promised. A number literal is a
decimal literal under that adapter. So an adapter is native to the language rather than an escape
hatch added to it.

---

## 6. What this architecture does not reach

- **Relational separation.** Every phase reads one name at a time. A pair separated only by a
  correlation between two names is unreachable.
- **An adapter's value side where the caller states no domain.** The top is forced there, and it
  is the honest answer: nobody can decide it.
- **The concrete meet's exactness.** It keeps its law. The abstract meet sits beside it and does
  not weaken it.
- **A top in the term language.** Forced, for the reason in section 2.
