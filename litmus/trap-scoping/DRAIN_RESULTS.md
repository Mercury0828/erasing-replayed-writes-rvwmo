# Drain differential (Table 7 of the paper)

The three tests of this directory are run under the two completions of the trap boundary, the Cat models
`litmus/cat/riscv_s1v2_nodrain.cat` (no ordering added at the trap) and `litmus/cat/riscv_s1v2_drain.cat`
(strict drain: every access before a trap entry is ordered before every access after the matching return).
Everything else is held fixed.

```
cd $ISLA_ROOT
for t in S1v2_trap_mp S1v2_control_notrap S1v2_control_fence; do
  for c in nodrain drain; do
    ./target/release/isla-axiomatic -A $ISLA_IR -C $ARTIFACT_ROOT/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml \
      --footprint-config $ARTIFACT_ROOT/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml \
      -m $ARTIFACT_ROOT/litmus/cat/riscv_s1v2_$c.cat -s 60 -T 4 $ARTIFACT_ROOT/litmus/trap-scoping/$t.toml
  done
done
```

Recorded verdicts (verbatim Isla summary lines, budget 60 s and 4 solver threads):

| Test | No-drain completion | Strict-drain completion |
|---|---|---|
| `S1v2_trap_mp` (trap between the two stores of hart 0) | `S1v2_trap_mp allowed (14 of 14) 53952ms` | `S1v2_trap_mp forbidden (0 of 14) 96260ms` |
| `S1v2_control_notrap` (faulting store removed) | `S1v2_control_notrap allowed (8 of 8) 5089ms` | `S1v2_control_notrap allowed (8 of 8) 6239ms` |
| `S1v2_control_fence` (explicit `fence rw,rw`) | `S1v2_control_fence forbidden (0 of 16) 66740ms` | `S1v2_control_fence forbidden (0 of 16) 82946ms` |

The final condition of all three tests is the message-passing outcome in which hart 1 sees the flag and not the data.

## Program-order commitment

The configuration `litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml` is a copy of
`riscv64_g2_trap_umode_defaults.toml` with one change:

```toml
in_program_order = ["sail_barrier", "sail_trap", "sail_mret", "sail_write_CSR"]
```

Isla relates two events by `po` only if both are memory events or are marked `in_program_order`
(`isla-axiomatic/src/axiomatic.rs`, function `po`), and an abstract event is marked only if its name is listed under
this key (`isla-lib/src/config.rs`, `get_in_program_order`). With only `"sail_barrier"` listed, the trap entry,
return and CSR-write events are present in the IR `rv64d_g58.ir` (which declares the abstract events `sail_trap`,
`sail_mret` and `sail_write_CSR`) but are related by `po` to no event, so every trap-derived relation is empty.

This change is a modelling commitment, not a neutral tooling fix: declaring the trap events to be in program order
is the executable form of the assumption that program order survives trap, handler and replay. The differential
above should therefore be read as follows: given this commitment, the no-drain and strict-drain completions are
observationally separable on the Sail model. It is not evidence for the commitment itself, and it does not show that
RVWMO guarantees the no-drain outcome. No Sail source and no IR was modified for this experiment.
