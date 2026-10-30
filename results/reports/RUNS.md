# Simulation runs behind the paper

Software: HyperCloud 0.5.1 with HyperCloudCore 0.7.8, plotting with PDEStudioCore 0.4.2. All results of the paper
come from one run of all studies on HyperCloudCore 0.7.8 (29 Oct 2026).

| Study | Hardware, precision | Tables |
|---|---|---|
| Convergence (advection, Burgers; 1-D and 2-D) | CPU, Float64 | `2026-10-29-rerun-078-tables.md`, section "Convergence" |
| Conservation defect | CPU, Float64 | `2026-10-29-conservation-defect-tables-078.md` |
| Sod shock tube (1-D) | workstation CPU, Float64 | `2026-10-29-sod1d.md` |
| Double Mach reflection, Mach 3 step, 2-D Riemann problem | GPU (CUDA), Float32 | `2026-10-29-rerun-078-tables.md`, section "Euler shock problems" |
| Isentropic vortex | GPU and CPU, Float32 | `2026-10-29-rerun-078-tables.md`, section "Isentropic vortex" |

`2026-10-29-rerun-078-results.txt` holds the one-line summary of every run of that rerun (`<job id> <summary>`: method,
resolution, status, minimum density/pressure, mass change, number of steps). It also contains runs of studies that
are not part of this paper (particle management, BGK on moving clouds).

The run configurations for each figure are in `../configs/` (`*_source_N.jl`; paths in them are relative to the
root of the HyperCloud simulations project).
