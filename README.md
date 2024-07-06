# Linear logic prover

This is a prover for the multiplicative fragment (tensor, implication) of linear logic. The proof search is done in sequent calcucus with no heuristics, to find all possible proofs. The prover is therefore relatively slow. It then converts those proofs to natural deduction proofs with proof terms. It optionally normalises and discards any identical proofs (since the mapping from sequent-style proofs to natural deduction proofs is many-to-one). The resulting proofs are written to a latex file which is compiled.

## Options

| option | longer version of the parameter | used to  |
| :---   | :-| :- |
| -i | --infile | File which holds the sequent to be proven. Default = `sys.stdin`|
| -o | --outfile | Latex file to which the proof is written. Default = `proof.tex` |
| -s | --sequents | Prints the original sequent calculus proofs too. |
| -a | --all | Prints all the natural deduction proofs (no normalisation) |

## Syntax

The prover expects a comma separated list of linear logic formulae. The last formula is interpreted as the proof goals and any preceding formulae as the premises of the proof. The connectives are written `-o` (linear implication) and `*` (multiplicative conjunction). Proof terms for the premises can be given separated by `:`, e.g. `V : e -o t`. 

## Example usage

`echo "A -o A " | python prover.py` proves `A -o A` from no premises.

`echo "V:A -o B -o T, Q1:(A -o T) -o T, Q2:(B -o T) -o T, T"| python prover.py ` proves `T` from `A -o B -o T`, `(A -o T) -o T` and `(B -o T) -o T`.

`echo "V: E1 -o E2 -o T, Q1:(E1 -o T) -o T, Q2:(E2 -o (T * l)) -o T, L: E1 -o (E1 * l), T" | python prover.py ` proves `T` from `E1 -o E2 -o T`, `(E1 -o T) -o T`, `(E2 -o (T * l)) -o T` and `E1 -o (E1 * l)`. (This takes a while.)
