# Examples

Every file in this directory parses and runs with the current checker.
Run one with:

```
cabal run detour -- examples/<file>.dt
```

| File | What it shows |
| ---- | ------------- |
| `simplest.dt` | Minimal theorem: `⊤` by `⊤-intro`. |
| `impl.dt` | Implication intro/elim chain (`A ==> B ==> C ⊢ B ==> A ==> C`). |
| `axioms.dt` | Declared axioms with `∀-elim` / `==>-elim`. |
| `axioms-only.dt` | Module with axioms but no theorems; checks vacuously. |
| `exists-intro.dt` | `∃`-introduction. |
| `modus-ponens.dt` | Second-order theorem schema (`for all propositions …`) and its reuse via a single `by theorem` justification. |
| `naturals.dt` | Peano naturals and addition as axioms, with a hand-written totality proof. |
| `naturals-typed.dt` | Same, with an induction axiom instead of a manual proof. |
| `naturals-rules.dt` | Custom `syntax`, `judgment`, and `rule schema` declarations, incl. case analysis. |
| `sum-induction.dt` | Addition totality proved by explicit `by induction` with `Zero` / `Suc` cases. |
| `sum-uniq.dt` | Larger development reusing lemmas — note it admits two lemmas `by unproved` (see below). |
| `sum-auto.dt` | **Interactive.** `prove` automation over the same theory: the tool searches and prompts for guidance — the mixed-initiative workflow from the paper. Run it in a terminal and answer the prompts. |
| `wrong-exists-intro.dt` | **Negative.** Faulty `∃`-intro the checker must reject. |
| `wrong-exists-elim.dt` | **Negative.** Faulty `∃`-elim the checker must reject. |
| `wrong-forall-intro.dt` | **Negative.** Leaking eigenvariable in `∀`-intro the checker must reject. |

Two caveats, inherited from the prototype: `by unproved` silently admits any goal
(used for two lemmas in `sum-uniq.dt`), and custom rules are trusted without
validity checking. A `✅` therefore means "no rule was violated", not "true".
See [`archive/`](./archive/) for historical sketches that no longer parse.
