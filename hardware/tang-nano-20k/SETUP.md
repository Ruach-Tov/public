# Tang Nano 20K — Setup Notes

## Source Layout

RTL, synthesis scripts, and formal-verification harnesses for the sorting-network
work described in these notes live in subdirectories alongside this file:

- **`rtl/`** — Verilog sources: `sorting_network_n16.v`, `sorting_network_n16_d9.v`
  (depth-9 variant), `bitonic_sort_n16.v`, `dobbelaere_n16.v`,
  `formal_sorting_network_n16.v`, single-comparator width variants
  (`single_cas_w{1,2,3,4,8}.v`), and Gowin ALU-synthesis netlist references.
- **`synth/`** — Yosys scripts for the ALU-vs-generic sweeps and critical-path
  analysis: `synth_gowin_w{2,4,8,32}.ys`, `synth_cas_{alu,clean,gowin,gowin_alu}_w*.ys`,
  `crit_w{2,4,8,32}.ys`, `depth_w{1,2,4,8,16,32}.ys` and related.
- **`formal/`** — SymbiYosys formal-verification harness:
  `formal_sorting_network_n16.sby` (targets `formal_sorting_network_n16.v` in `rtl/`).

Recovered from `/tmp` on 15 August 2026 (see the earlier holding location at
`research/sorting-networks/fpga-recovered/README.md` for the recovery narrative).

## USB Detection
✅ Device detected: `Bus 001 Device 032: ID 0403:6010 Future Technology Devices International, Ltd FT2232C/D/H`

## NixOS Configuration Needed

Add to `/etc/nixos/configuration.nix`:

```nix
services.udev.extraRules = ''
  # Sipeed Tang Nano 20K (FT2232 JTAG/UART)
  ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6010", MODE="0666", GROUP="plugdev"
'';
```

Then: `sudo nixos-rebuild switch`

## Open Source Toolchain

### Synthesis (working NOW):
```bash
nix-shell -p yosys
yosys -p "read_verilog sorting_network_n16.v; synth_gowin -top sorting_network_n16 -json output.json"
```

### Place & Route (BLOCKED):
nextpnr-himbaechel 0.8 (in nix) doesn't have the exact package database for the
Tang Nano 20K's Gowin part.  Need: apicula ≥ 0.32 chipdb, or build nextpnr from
source with latest apicula.

Alternative: `pip install apycula` (0.32), then use gowin_pack to generate
bitstream after nextpnr.

**Part number caveat:** notes from earlier work variously cited `GW2AR-LV18QN88`,
`GW2A-18`, `GW2A-18C`, `GW2AR-LV18QN88C7/I6`, and `GW2AR-LV18QN88C8/I7`.  These
disagree on the die suffix and speed grade.  The board silkscreen is the ground
truth — inspect physically before trusting any of the above.  If the correct
apicula chipdb key turns out to be `GW2A-18C`, that may be what unblocks P&R.

### Programming (ready):
```bash
nix-shell -p openfpgaloader
openFPGALoader --board tangnano20k bitstream.fs
```

## Gowin Synthesis Results (with ALU inference)

| Width | ALU  | LUT3 | LUT2 | DFF  | Total  | % of 20K |
|-------|------|------|------|------|--------|----------|
| 4-bit |  240 |  360 |  120 |  715 | 1,570  |    7.6%  |
| 8-bit |  480 |  840 |  120 | 1,419| 3,122  |   15.1%  |
| 16-bit|  960 | 1800 |  120 | 2,827| 6,226  |   30.0%  |
| 32-bit| 1920 | 3720 |  120 | 5,643| 12,434 |   60.0%  |

ALU cells use the hard carry chain for comparison — much faster than LUT cascade.
