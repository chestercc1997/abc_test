# NPN Half-adder/Full-adder Detection

### Usage

```bash
./abc -c "gen -m 8.blif"
```
```bash
./abc -c "r 8.blif;st;&get;&detect_faha "
```

### Description

The results will be shown in `detect_faha_output.json`.

This tool identifies all XOR gates (including `xor2`, `xor3`, and `xor_all`) based on the cut enumeration functionality. Specifically:

*   **`xor_all`**: Represents all `xor2` and `xor3` gates.
*   **`xor_remaining`**: Represents all XOR gates except those used in half adders (HA) and full adders (FA).

Each detected half adder and full adder is grouped together, and the corresponding AIG node indices for each group are displayed, with groups separated by a `0`.

> **Note**: The identified half adders and full adders are NPN-equivalent.