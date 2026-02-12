Defined `FinEncoding` for `Literal` and `CNF` in `botlib/Complexity/SAT.lean`.

The implementation includes:
- `literalFinEncoding`: A finite encoding for `Literal` using the standard Turing machine alphabet `Γ'`. Positive literals are prefixed with `Γ'.bit true` and negative literals with `Γ'.bit false`.
- `listEncoding`: A generic combinator that creates a `FinEncoding (List α)` from a `FinEncoding α` by using `Option ea.Γ` as the alphabet, where `none` serves as an element separator.
- `clauseFinEncoding` and `cnfFinEncoding`: Derived encodings for `Clause` and `CNF` using the `listEncoding` combinator.

All definitions are accompanied by proofs of the `decode_encode` invariant, and the file compiles successfully with `lake build`.

```json
{
  "status": "completed",
  "summary": "Defined FinEncoding for Literal and CNF in SAT.lean. lake build succeeds.",
  "details": "Implemented literalFinEncoding, listEncoding (generic), clauseFinEncoding, and cnfFinEncoding. Verified correct decoding with proofs for each encoding. Created private helper splitByNone for the list decoding logic."
}
```

