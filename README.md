# Linear logic prover

This is a prover for the multiplicative intuitionistic linear logic (with tensor, implication and 1). The proof search is done in sequent calcucus. At each step when the premises need to be split (by the left implication or the right tensor rule), the prover checks for each possible split whether the polarity of all the atomic formulae is balanced and gives up on branches where this is not the case.

On the default behaviour, the prover converts the sequent calculus proofs to natural deduction proofs with proof terms, normalises them and any identical proofs (since the mapping from sequent-style proofs to natural deduction proofs is many-to-one). The resulting proofs are written to a latex file which is compiled. You can configure this behaviour with various options.

## Options

| option | longer version of the parameter | used to  |
| :---   | :-| :- |
| -i | --infile | File which holds the sequent to be proven. Default = `sys.stdin`|
| -o | --outfile | Latex file to which the proof is written. Default = `proof.tex` |
| -s | --sequents | Prints the original sequent calculus proofs too. |
| -q | --only-sequents | Print *only* the sequent calculus proofs |
| -a | --all | Prints all the natural deduction proofs (no normalisation) |
| -r | --rescale | Scaling factor for the latex presentation of the proof, useful for big proofs. Default = 0.8 |
| -d | --dump-cache | Print the cache to `stdout` when done. For debugging |
| -p | --polarity | Print polarities of atomic formulae in original sequent |
| -n | --no-prune | Do not prune proof search by polarity balance. Mainly useful to test the efficiency of pruning |
| -l | --latex-off | Do not run latex |
| -t | --tensor-reduction | Reduce proof terms from tensor elimination. This leads to fewer distinct proofs/readings. Useful for some linguistic applications |

## Syntax

The prover expects a comma separated list of linear logic formulae. The last formula is interpreted as the proof goals and any preceding formulae as the premises of the proof. The connectives are written `-o` (linear implication) and `*` (multiplicative conjunction). Atomic formulae must start with a letter and be followed by alphanumeric characters. Unit (the identity for tensor) is written `1`. Proof terms for the premises can be given separated by `:`, e.g. `V : e -o t`. 

## Example usage

`echo "A -o A " | python prover.py` proves `A -o A` from no premises.

`echo "V:A -o B -o T, Q1:(A -o T) -o T, Q2:(B -o T) -o T, T"| python prover.py ` proves `T` from `A -o B -o T`, `(A -o T) -o T` and `(B -o T) -o T`.

`echo "(A * 1) -o A" | python prover.py` proves `(A * 1) -o A` from no premises. 

`echo "V: E1 -o E2 -o T, Q1:(E1 -o T) -o T, Q2:(E2 -o (T * l)) -o T, L: E1 -o (E1 * l), T" | python prover.py ` proves `T` from `E1 -o E2 -o T`, `(E1 -o T) -o T`, `(E2 -o (T * l)) -o T` and `E1 -o (E1 * l)`. 
