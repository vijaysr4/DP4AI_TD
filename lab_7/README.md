# TD 7 BMC & k-Induction Verification Tool

This repository contains a Python-based verification tool that uses **Bounded Model Checking (BMC)** and **k-induction** (with a simple path condition) to check safety properties of transition systems.

The tool is built on top of [pysmt](https://pysmt.readthedocs.io/) and expects input files in the VMT (Verification Modulo Theories) format. These files must contain:
- An initial condition annotated with `:init`
- A transition relation annotated with `:trans`
- A safety property (invariant) annotated with `:invar-property`
- “Next” state annotations for state variables (using `:next`)

## Repository Structure

- **bmc.py**: Main implementation of BMC and k-induction.
- **ts.py**: Transition system representation and VMT parsing utilities.
- **run_induction_tests.py** (optional): A script to run k-induction on a list of input files.
- **inputs/**: Directory containing example input files.
- **README.md**: This file.

## Usage
To run the BMC check up to a bound `k` (e.g., 10), use:

```
bash
python bmc.py --k 10 --input path/to/your_input_file.smt2
```
Output: 
```bash
Reading ./inputs/counter.smt2
Extra formula parsed as: (i__AT0 <= 2)
BMC check at bound 0:
No counterexample found at bound 0
BMC check at bound 1:
No counterexample found at bound 1
BMC check at bound 2:
No counterexample found at bound 2
BMC check at bound 3:
Counterexample found at bound 3
i__AT0_bmc_3 := 5
i__AT0_bmc_2 := 4
i__AT0_bmc_0 := 2
i__AT0_bmc_1 := 3

```
## Running k-Induction
To run k-induction (with the `--i True` flag), for example with a bound of 3:

```bash
python bmc.py --i True --k 3 --input path/to/your_input_file.vmt
```

Output:
```bash
Reading inputs/array_max-2.smt2
Skipping extra formula demonstration: 'i__AT0' not found in state variables.
Induction Base Check at bound 0:
No base case counterexample at bound 0
Inductive Step Check (KIND_0):
Inductive step failed: a counterexample for the induction step was found.
_PC.3_bmc_1 := True
__RET__$main_bmc_0 := 0.0
i__4$main_bmc_1 := 0.0
a2_bmc_0 := 0.0
tmp2__14$main_bmc_0 := 0.0
_PC.1_bmc_0 := True
a5_bmc_0 := 0.0
i__30$main_bmc_0 := 0.0
_PC.2_bmc_0 := True
val__27$main_bmc_1 := 0.0
__INLINE_TEMP__16$main_bmc_0 := 0.0
i__18$main_bmc_0 := 0.0
i__30$main_bmc_1 := 0.0
__RET__$main_bmc_1 := 0.0
val__8$main_bmc_0 := 0.0
i__4$main_bmc_0 := 0.0
__INLINE_TEMP__16$main_bmc_1 := 0.0
i__23$main_bmc_0 := 0.0
_PC.1_bmc_1 := False
__INLINE_TEMP__19$main_bmc_0 := 0.0
a0_bmc_0 := 0.0
a5_bmc_1 := 0.0
_PC.2_bmc_1 := False
_PC.0_bmc_1 := True
idx__2$main_bmc_0 := 0.0
__INLINE_TEMP__36$main_bmc_0 := 0.0
a0_bmc_1 := 0.0
a4_bmc_0 := 0.0
_PC.3_bmc_0 := False
val__24$main_bmc_1 := 0.0
a3_bmc_0 := 0.0
tmp1__12$main_bmc_0 := 0.0
_PC.0_bmc_0 := False
__INLINE_TEMP__36$main_bmc_1 := 0.0
x__10$main_bmc_0 := 0.0
a1_bmc_0 := 0.0
i__7$main_bmc_1 := 0.0
max_bmc_1 := 0.0
i__18$main_bmc_1 := 0.0
maxval__34$main_bmc_1 := 0.0
i__23$main_bmc_1 := 0.0
val__8$main_bmc_1 := 0.0
maxval__34$main_bmc_0 := 0.0
a3_bmc_1 := 0.0
i__7$main_bmc_0 := 0.0
val__27$main_bmc_0 := 0.0
i__38$main_bmc_1 := 0.0
a4_bmc_1 := 0.0
x__10$main_bmc_1 := 0.0
tmp__32$main_bmc_1 := 0.0
i__38$main_bmc_0 := 0.0
tmp2__14$main_bmc_1 := 0.0
a6_bmc_0 := 0.0
tmp1__12$main_bmc_1 := 0.0
tmp__32$main_bmc_0 := 0.0
idx__2$main_bmc_1 := 0.0
a6_bmc_1 := 0.0
val__24$main_bmc_0 := 0.0
a1_bmc_1 := 0.0
a2_bmc_1 := 0.0
__INLINE_TEMP__19$main_bmc_1 := 0.0
max_bmc_0 := 0.0
```
