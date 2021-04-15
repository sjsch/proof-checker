# Proof checker
Connor Cahoon, Sam Schweigel
****
### Running:
The proof checker can be run from the command line using the command:

        > swpl naturaldeduction.pl proof.txt

### Syntax

The proof file provided by the user should obey the following syntax.

- The file should be composed of only axioms and proofs
- An axiom is of the format: "axiom [name] : [logical argument]"
- A proof is of the format: "proof [name] : [logical argument] { [proof terms] }"

**ex.**

    axiom and_comm : P /\ Q -> Q /\ P
    proof and_comm : P /\ Q -> Q /\ P {
        cond (hyp_pq) {
            conj {
              proj_right { hyp_pq }
            } {
              proj_left { hyp_pq }
            }
        }
    }

### Proof terms

There are 21 different terms usable in a proof. To view their use syntax and implementation see proofterm() in naturaldeduction.pl

### Future work

Progress has been made in implementing a calculus of constructions proof checker. For it to be functional a parser would need to be written. Additionally, due to the nature of the calculus of constructions, an incorrect proof provided by the user could stall the checker, and a solution should be found before it could be complete.
