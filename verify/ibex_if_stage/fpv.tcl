
analyze -sv12 \
    +incdir+/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/ \
    +incdir+/data/fhj/sva-var/ibex/vendor/lowrisc_ip/dv/sv/dv_utils/ \
    +incdir+/data/fhj/sva-var/ibex/rtl/ \
    -f /data/fhj/sva-var/jg_test/ibex.f

elaborate -top ibex_if_stage

clock clk_i
reset ~rst_ni

prove -all