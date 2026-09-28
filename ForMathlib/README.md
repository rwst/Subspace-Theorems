# ForMathlib: general material Mathlib lacks

A library (`lean_lib ForMathlib`) of definitions and results that are not specific to one paper
or roadmap, and that Mathlib does not have. It is held to the rules of the other libraries (no
`sorry`, no `set_option`, std3 axioms, fine-grained imports, module system, Mathlib root
namespaces). Its files follow Mathlib's directory layout, so each one is a candidate upstream
contribution. It is modelled on `ForMathlib/` of the author's `lean-code` corpus.

| file | content | used by |
| --- | --- | --- |
| `NumberTheory/PisotNumber.lean` | `IsPisot`, `IsSalem`; the golden ratio is Pisot | `CorvajaZannier2004`, `AdamczewskiBugeaud2007` (Theorem 5) |
| `Analysis/Real/BetaExpansion.lean` | Rényi's `β`-transformation and `β`-digits; the expansion converges | `AdamczewskiBugeaud2007` (Theorems 1A–5A) |

`IsPisot` was moved here from `CorvajaZannier2004/PseudoPisot.lean` unchanged, so the flat
Challenge of that paper, which repeats the definition verbatim, still matches.
