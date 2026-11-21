# Rebuilding the Isla model

The litmus tests of the paper run on Isla intermediate representations (IRs) of sail-riscv, built
as follows. Two IRs are used: `rv64d_g58.ir` (all three patches; the RVWMO calibration suite, the trap
suite, the drain differential and the early-write suite) and `rv64d.ir` (patch 1 only; the older
trap-scoping tests listed in `litmus/frozen-suite/run_repo_baseline.sh`). Neither IR (about 15 MB each)
is included; both are regenerated from the sources below.

## Versions

| Component | Version |
|---|---|
| sail-riscv | `bacam/sail-riscv`, branch `202606-isla` ("Add Isla cmake targets"), commit `7b12a05` |
| Sail | 0.20.1 (opam package `sail.0.20.1`, OCaml 4.13.1) |
| isla-sail plugin | from `rems-project/isla`, `isla-sail` at commit `7f6882b` |
| Isla | `rems-project/isla` at commit `7f6882b3f468fe34df38ae3ffc0aede5baa0e7d6` (the same checkout provides `isla-sail`), `cargo build --release` |
| Z3 | 4.8.12 |

## The three patches

Apply them in this order to a clean checkout of commit `7b12a05`:

1. `step_endcycle_isla_harness.patch` (`model/postlude/step.sail`). The symbolic step loop that Isla
   executes ends a cycle only when a hart waits. A retired instruction does not end one, so all
   instructions of a thread fall into one cycle and Isla rejects the test. The patch ends a cycle
   after every retired instruction.
2. `split_misaligned_footprint_fix.patch` (`model/sys/vmem_utils.sail`). It fixes the symbolic width
   of the misaligned-split path. Without it, four data-dependency tests of the calibration suite come
   out allowed against a forbidden reference.
3. `M3_g5_abstract_trap_events.patch`. It declares the trap-entry, exception-return and CSR-write
   events (`sail_trap`, `sail_mret`, `sail_write_CSR`) so that a Cat model can refer to them.

## Generating the IR

```bash
export ARTIFACT_ROOT=/path/to/this/artifact
export ISLA_ROOT=/path/to/isla                  # where Isla will be checked out
export ISLA_SNAPSHOTS=/path/to/ir-directory     # where the two IRs will be stored
export SAIL_SRC=/path/to/sail-riscv-src         # where sail-riscv will be checked out
mkdir -p "$ISLA_SNAPSHOTS"

# 1. build Isla and the isla-sail plugin against Sail 0.20.1; put both on PATH
git clone https://github.com/rems-project/isla.git "$ISLA_ROOT"
cd "$ISLA_ROOT" && git checkout 7f6882b
cargo build --release                           # -> target/release/isla-axiomatic, isla-footprint
cd "$ISLA_ROOT/isla-sail" && opam exec -- make  # -> _build/default/sail_plugin_isla.cmxs
export PATH="$ISLA_ROOT/target/release:$ISLA_ROOT/isla-sail:$PATH"
                                                # isla-sail = sail -plugin <that .cmxs> -isla

# 2. check out sail-riscv and apply patch 1
git clone https://github.com/bacam/sail-riscv.git "$SAIL_SRC"
cd "$SAIL_SRC" && git checkout 7b12a05
git apply "$ARTIFACT_ROOT/model/step_endcycle_isla_harness.patch"

# the IR generation command, with the configuration supplied as model/rv64d_v256_e64.json (the file
# the generated_isla_rv64d cmake target of the branch produces from its config template)
gen_ir () {
  cd "$SAIL_SRC/model" && mkdir -p out && cp "$ARTIFACT_ROOT/model/rv64d_v256_e64.json" out/
  isla-sail --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.1 \
    --isla-output-dir out -o rv64d --config out/rv64d_v256_e64.json --all-modules riscv.sail_project
}

# 3. rv64d.ir: patch 1 only
gen_ir && cp "$SAIL_SRC/model/out/rv64d.ir" "$ISLA_SNAPSHOTS/rv64d.ir"

# 4. rv64d_g58.ir: patches 1, 2 and 3
cd "$SAIL_SRC"
git apply "$ARTIFACT_ROOT/model/split_misaligned_footprint_fix.patch"
git apply "$ARTIFACT_ROOT/model/M3_g5_abstract_trap_events.patch"
gen_ir && cp "$SAIL_SRC/model/out/rv64d.ir" "$ISLA_SNAPSHOTS/rv64d_g58.ir"
export ISLA_IR="$ISLA_SNAPSHOTS/rv64d_g58.ir"
```

## Checks

- `cd "$ISLA_ROOT" && isla-footprint -A "$ISLA_SNAPSHOTS/rv64d_g58.ir" -C configs/riscv64_g2.toml -i "sw x7, 0(x8)"`
  returns write-memory events (with `rv64d.ir`, which lacks patch 2, it fails).
- With `litmus/cat/riscv_trap.cat`, the test `litmus/trap-scoping/trap_store_faultB2_replay.toml` is
  forbidden (0 of 7); the tripwire axiom in that Cat file fires only when the trap events of patch 3
  are present.
