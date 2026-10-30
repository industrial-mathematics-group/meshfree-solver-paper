# DMR_1440x450: the runs of the HyperCloudCore 0.7.8 rerun (results/reports/RUNS.md), GPU (CUDA), Float32,
# 1440x450, CFL 0.8, with exactly the parameters of the runs.
module _DMR_1440x450_Base
    using HyperCloud, StaticArrays
    Base.include(@__MODULE__, joinpath(@__DIR__, "DMR.jl"))
end

function get_config()
    config = _DMR_1440x450_Base.euler_2d_DMR()
    merge!(config.shared, Dict{Symbol, Any}(:T => Float32, :Grid_Ns => (1440, 450), :Time_CFL => 0.8))
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
                              "RK4SSPMUSCL4(EPD2,AR,MLS2)",
                              "RK4SSPMUSCL4(EPD2,AR,MLS4)",
                              "RK4SSPMUSCL4(EPD2,RU,MLS2)"])
    push!(config.sources, @__FILE__)
    return config
end
