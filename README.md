# Cartesian Frames in HOL

This repository contains a formalisation in [HOL](https://hol-theorem-prover.org) of the results in the [Cartesian Frames sequence](https://www.alignmentforum.org/s/2A7rrZ4ySx6R8mfoT).

The proofs have been checked to build with [this commit](https://github.com/HOL-Theorem-Prover/HOL/tree/c51de550191d516cb9dfe47c6a1e866b232f2c96) of the HOL theorem prover.
They may also work in other versions, but beware that proof scripts can be fragile to changes in the underlying prover libraries.

# Contents

The theories are organised (for the most part) so that the general theorems from the {n+1}th blog post in the sequence are proved in the theory named `cfn` with specific examples formalised in the theory named `exn`.
Thus for example the proof script for the first (subagent) decomposition theorem, which appears in the ninth blog post, is in `cf8Script.sml`.

# Building the theories

To check the proofs yourself:

1. Get the HOL theorem prover.
   For example, follow [the instructions](https://hol-theorem-prover.org/#get) on its website.
   (The extra details in the [CakeML build instructions](https://github.com/CakeML/cakeml/blob/master/build-instructions.sh) may be useful, but note that CakeML is not required for the Cartesian frames proofs.)
2. Run `Holmake` (or `$HOLDIR/bin/Holmake`) in this directory.
   To build only a specific theory (and its dependencies), for example `cf8`, run `Holmake cf8Theory`.

# Interacting with and extending the theories

HOL is an interactive theorem prover.
Most of the value of this formalisation comes from interacting with it.
Pointers for how to do this can be found on [HOL's website](https://hol-theorem-prover.org/#doc).
