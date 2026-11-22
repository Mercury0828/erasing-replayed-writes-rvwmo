# Artifact: Erasing Replayed Writes under RVWMO

This is the artifact of the paper

> Jiachen Shen and Hui Zhong. *Erasing Replayed Writes under RVWMO: A Mechanized Contraction Theorem.*
> Submitted to the Journal of Automated Reasoning.

Archived on Zenodo: version v1.0.1, DOI [10.5281/zenodo.24432911](https://doi.org/10.5281/zenodo.24432911)
(all versions: [10.5281/zenodo.24412450](https://doi.org/10.5281/zenodo.24412450)).

It contains the Rocq development, the 100 Isla litmus tests with their verbatim results, the Sail
patches used to build the Isla model, and the simulator runs of the fault, repair and replay path.

## Contents

| Path | Contents | Paper |
|---|---|---|
| `rocq/` | The Rocq development (58 files, Coq 8.15.0) and `verify.sh`. `VERIFY_LOG.txt` is the output of `verify.sh` for this version. | Sections 3 to 7, Appendix B |
| `litmus/rvwmo-suite/` | The 36 standard RVWMO tests (calibration). | Section 8.2, Online Resource 1 |
| `litmus/frozen-suite/` | The 33 tests of the trap suite, their templates (`TEMPLATES.md`), run scripts and results (`RESULTS.md`). | Sections 8.3, 8.5, 8.8, Online Resource 1 |
| `litmus/trap-scoping/` | The earlier trap-scoping tests (11 runnable, 2 diagnostics), the tests of the drain differential, and the Isla configurations. | Sections 8.6, 8.8 |
| `litmus/early-write/` | The 20 tests of the early-write suite, the run scripts, the raw results and the diagnostics (`diag/`). `RESULTS.md` records every run, and `dropped/` keeps the first final-memory tests, which carried loads of the lanes and were replaced (Section 8.4). | Section 8.4, Table 5 |
| `litmus/cat/` | The Cat models: the no-drain and strict-drain completions and the trap tripwire. | Section 8.1 |
| `model/` | The three Sail patches and `REBUILD.md`, the recipe for the Isla model. | Section 8.1 |
| `sim/` | The test program, the handler of Section 8.7, the measurement handler, the run harness and the traces of the five `sail_riscv_sim` runs; `handler_regs_cert.sh` checks the handler against the schema α. | Sections 8.3, 8.7 |

## Checking the proofs

Requires Coq 8.15.0 (for example from opam: `opam install coq.8.15.0`).

```
cd rocq
bash verify.sh
```

`verify.sh` deletes all compiled files, builds the 58 files in dependency order and runs
`Print Assumptions` on 109 headline results. It exits with status 0 and prints
`ALL GREEN: 58 files build, 109 headline theorems 0-axiom.` when every file builds and every headline
result is closed under the global context. `make` builds the same files through `_CoqProject`.

The numbered results of the paper and the Rocq theorems that prove them (Table B1 of the paper):

| Result | Rocq theorems (files) |
|---|---|
| Lemma 1 | `rvwmo_perbyte_coherence` (`Perbyte.v`); `FRfF_in_gmo`, `fault_main_from_gmo` (`Gmo_consistency.v`) |
| mixed-size example | `ex_perbyte_ok`, `ex_union_cycle` (`Perbyte_example.v`) |
| Theorem 2, part 1 | `ML_T1_gmo` (`Gmo_consistency.v`) |
| Theorem 2, parts 2-4 | `ML_T1_refinement_pb` (`Perbyte.v`); one pair: `ML_T1_covers_single_lane` (`ML_T1.v`) |
| global adjacency fails | `natural_order_breaks_global_adj` (`ML_instance.v`) |
| ppo, rule r2 | `r2N_sub_r2F` (`PPO_frozen.v`); `alleged_counterexample_is_cyclic` (`R2_counterexample.v`) |
| Proposition 3 | `gamma_adj_needed_obs` (`Gamma_adj_obs.v`); `gamma_adj_needed_full` (`Gamma_adj_needed.v`) |
| Proposition 4 | `gamma_D_implies_gamma_adj` (`L2_gamma.v`); trap-and-replay instance `sw_instance_adj` (`Single_writer_instance.v`) |
| pair clauses derived | `po_twin_derived`, `dup_r12_derived` (`Token_model.v`); `alpha_regs_gives_Dup` (`Alpha_regs.v`) |
| trap erasure | `general_ctx_erasure` (`Ctx_erasure.v`); `ML_stage2_endtoend_pb` (`Perbyte.v`) |
| Theorem 5 | `stage2_shape`, `gen_shape_pos`, `pmp_shape_lanes` (`Shape.v`); `gen_ppo_in_gmo`, `gen_load_value` (`Gmo_counterpart.v`) |
| PMP matching rule | `allows_iff_deciding_full`, `spec_example_denied` (`Pmp_partial.v`) |
| unit-stride instances | `ml2_T1_pb_instance`, `ml2_instance_observation` (`ML_instance_2h.v`); `ml2_stage2_shape_instance`, `mu_stage2_shape_instance`, `unit_shape_GenStore_iff` (`Shape_instances.v`); `mu_po_not_total` (`ML_instance_unord.v`); `ml2_T1_gmo_instance` (`Gmo_instances.v`) |
| masked instance | `mk_T1_pb_instance`, `mk_stage2_shape_instance`, `mk_instance_observation`, `mk_shape_not_unit`, `mk_shape_is_reg_shape`, `mk_replay_same_shape` (`ML_instance_masked.v`); `mask_shape_from_regs` (`Shape_instances.v`); `mk_T1_gmo_instance` (`Gmo_instances.v`) |
| handler registers | `ar_i_alpha_fails_when_data_clobbered` (`Alpha_regs_instance.v`) |

`print_assumptions_full.sh` prints the raw `Print Assumptions` output of every headline result.

The comments in the Rocq sources are working notes written during the development. The statements
and proofs are what `verify.sh` checks.

## Running the litmus tests

The tests need Isla, Z3 4.8.12 and the Isla model of sail-riscv built as described in
`model/REBUILD.md`. The run scripts read these variables:

```
export ARTIFACT_ROOT=$(pwd)                                 # the root of this artifact
export ISLA_ROOT=/path/to/isla                              # Isla checkout at commit 7f6882b (model/REBUILD.md)
export ISLA_SNAPSHOTS=/path/to/ir-directory                 # directory holding the two regenerated IRs
export ISLA=/path/to/isla/target/release/isla-axiomatic     # default: $ISLA_ROOT/...
export ISLA_IR=/path/to/rv64d_g58.ir                        # default: $ISLA_SNAPSHOTS/rv64d_g58.ir
export ISLA_IR_OLD=/path/to/rv64d.ir                        # default: $ISLA_SNAPSHOTS/rv64d.ir
export OUT_DIR=/path/to/output-directory                    # default: the current directory
```

Examples:

```
# trap suite (Section 8.5): one verdict line per test
bash litmus/frozen-suite/run_frozen_suite.sh out.txt litmus/frozen-suite/FT*.toml

# early-write suite (Section 8.4) with Z3's macro finder, budget 2400 s, 6 solver threads
bash litmus/early-write/run_ew.sh -x litmus/early-write/macro_finder.smt2 out.txt 2400 6 \
     $(sed 's|.*|litmus/early-write/&.toml|' litmus/early-write/LIST.txt)

# calibration suite and earlier trap-scoping tests (Section 8.2), then the comparison with herd
bash litmus/frozen-suite/run_baseline_all.sh
bash litmus/rvwmo-suite/compare_refs.sh "$OUT_DIR/baseline_rvwmo.txt"     # the recorded run: 35 of 36 agree
```

Each script writes the verbatim Isla summary line of each test, for example
`EW_BF_r575 allowed (32 of 32)`. The recorded runs are in the `RESULTS*.md` and `*_raw.txt` files
next to the tests. Running times depend on the host and on the solver budget; the paper reports the
budgets used.

## Simulator runs

`sim/run_dr2.sh` assembles `sim/test.S` for the five configurations of Section 8.3 with GNU binutils
2.35.1 and runs each on the released `sail_riscv_sim` 0.13 with VLEN = 128. Set `SAIL_RISCV_SIM` to the
simulator binary. The `*.trace.log` and `*.stdout.log` files are the recorded traces, and
`results.txt` the recorded outcomes; the script overwrites them, so run it on a copy of `sim/`. `sim/test_contract.S` carries the three-instruction handler of
the contract, and `bash sim/handler_regs_cert.sh` (run from the artifact root) assembles it,
disassembles it and checks every architectural location it writes against α.

Machine-local paths of the original runs are written as `$ISLA_ROOT`, `$ISLA_SNAPSHOTS` and `$ARTIFACT_ROOT`
in the scripts and the recorded logs. `litmus/rvwmo-suite/REFERENCE.md` gives the reference verdict
of every calibration test, and `litmus/trap-scoping/DRAIN_RESULTS.md` the six verdicts and the command of the drain
differential.

## License

The Rocq development, the scripts, the authored litmus tests (trap suite, trap-scoping and early-write suites)
and the documentation are under the MIT licence (`LICENSE`). Third-party material keeps its own licence, and the full licence texts are in `LICENSES/`:
the 36 calibration tests in `litmus/rvwmo-suite/` and their herd reference results (`refs_herd.txt`) come from Isla
(`test/axiomatic/`), which derives them from the litmus-tests-riscv project (BSD-2-Clause,
`LICENSES/litmus-tests-riscv-BSD-2-Clause.txt`); the five Cat models in `litmus/cat/` contain the RVWMO Cat model
of herdtools as distributed with Isla (`web/client/dist/riscv.cat`, listed in Isla's `THIRD_PARTY_FILES.md` as
CeCILL-B, from herdtools), and these five files are distributed under the CeCILL-B licence
(`LICENSES/herdtools-CeCILL-B.txt`); the Isla configurations `litmus/trap-scoping/riscv64_g2_*.toml` extend Isla's
`configs/riscv64_g2.toml` (Isla: BSD-2-Clause, `LICENSES/isla-BSD-2-Clause.txt`); the three patches in `model/`
modify sail-riscv and are under its licence, and `model/rv64d_v256_e64.json` is generated from the sail-riscv
configuration template (sail-riscv: BSD-2-Clause, `LICENSES/sail-riscv-BSD-2-Clause.txt`).

The figures of the paper are diagrams drawn for the paper; they show no measured data.
