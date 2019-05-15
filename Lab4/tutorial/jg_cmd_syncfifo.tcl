clear -all
analyze -v2k sync_fifo.v
analyze -sv wrapper_sync_fifo.sv
elaborate -top sync_fifo
clock clock
reset reset
prove -bg -all
