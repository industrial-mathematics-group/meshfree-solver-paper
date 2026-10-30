# Mach3Step_900x300: the runs of the HyperCloudCore 0.7.8 rerun (results/reports/RUNS.md), GPU (CUDA), Float32,
# 900x300, CFL 0.8, with exactly the parameters of the runs.
module _Mach3Step_900x300_Base
    using HyperCloud, StaticArrays
    Base.include(@__MODULE__, joinpath(@__DIR__, "Mach3Step.jl"))
end

function get_config()
    config = _Mach3Step_900x300_Base.euler_2d_mach3step()
    merge!(config.shared, Dict{Symbol, Any}(:T => Float32, :Grid_Ns => (900, 300), :Time_CFL => 0.8))
    config.defaults = Symbol.(["RK2MUSCL1",
                              "RK2MUSCL2(EPD1,AR,MLS2)",
                              "RK2MUSCL2(EPD2,AR,MLS2)",
                              "RK2MUSCL2(VK,AR,MLS2)",
                              "RK2MUSCL2(EPD2,RU,MLS2)",
                              "RK3MUSCL3(EPD1,AR,MLS2)",
                              "RK3MUSCL3(EPD1,AR,MLS3)",
                              "RK3MUSCL3(EPD1,AR,MLS0)",
                              "RK3MUSCL3(EPD2,AR,MLS2)",
                              "RK3MUSCL3(EPD2,AR,MLS3)",
                              "RK3MUSCL3(EPD2,AR,MLS0)",
                              "RK3MUSCL3(EPD2,RU,MLS2)",
                              "RK4SSPMUSCL4(EPD1,AR,MLS2)",
                              "RK4SSPMUSCL4(EPD1,AR,MLS4)",
                              "RK4SSPMUSCL4(EPD1,AR,MLS0)",
                              "RK4SSPMUSCL4(EPD2,AR,MLS2)",
                              "RK4SSPMUSCL4(EPD2,AR,MLS4)",
                              "RK4SSPMUSCL4(EPD2,AR,MLS0)",
                              "RK4SSPMUSCL4(EPD2,RU,MLS2)"])
    push!(config.sources, @__FILE__)
    return config
end
