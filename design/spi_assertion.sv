parameter CLK_DIV = 4;
parameter sclk_period = 2*CLK_DIV;
//CLK_DIV == 4

//when there is data chg, the busy must be always HIGH
//CHP 1: Data transfer (mosi)
property bus_high;
	@(negedge spi_vif.clk) 
	( $rose(spi_vif.mosi) || $fell(spi_vif.mosi) ) |-> (spi_vif.busy);
endproperty

property cs_low;
	@(negedge spi_vif.clk) 
	( $rose(spi_vif.mosi) || $fell(spi_vif.mosi) ) |-> !(spi_vif.cs_n);
endproperty

//cs rose tgt as done signal asserted
property cs_aligned_done;
	@(negedge spi_vif.clk) 
	( $rose(spi_vif.done) ) |-> $rose(spi_vif.cs_n);
endproperty

//data update only when done rose
property rxdata_timing;
	@(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
	!($rose(spi_vif.done) ) |-> $stable(spi_vif.rx_data);
endproperty

//sclk no glitch
property sclk_glitch_rose;
	@(negedge spi_vif.clk) disable iff (!spi_vif.busy)
	$rose(spi_vif.sclk) |-> ##4 $fell(spi_vif.sclk);
endproperty

property sclk_glitch_fell;
	@(negedge spi_vif.clk) disable iff (!spi_vif.busy)
	$fell(spi_vif.sclk) |-> ##4 $rose(spi_vif.sclk);
endproperty

assert_bus_high: assert property(bus_high);
assert_cs_low: assert property(cs_low);
assert_cs_aligned_done: assert property(cs_aligned_done);
assert_rxdata_timing: assert property(rxdata_timing);
assert_sclk_glitch_rose: assert property(sclk_glitch_rose);
assert_sclk_glitch_fell: assert property(sclk_glitch_fell);
