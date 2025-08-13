parameter CLK_DIV = 4;
parameter SCLK_PERIOD = 2*CLK_DIV;
//CLK_DIV == 4

property reset;
	@(posedge spi_vif.clk)
	(!spi_vif.rst_n) |-> (  spi_vif.busy 	== 0 &&
				spi_vif.sclk 	== 0 &&
				spi_vif.cs_n 	== 1 &&
				spi_vif.done	== 0 &&
				spi_vif.rx_data == 0
				);
endproperty
//when there is data chg, the busy must be always HIGH
//CHP 1: Data transfer (mosi)
property bus_high;
	@(negedge spi_vif.clk)
	( $rose(spi_vif.mosi) || $fell(spi_vif.mosi) ) |-> (spi_vif.busy);
endproperty

property busy_deassert;
	@(negedge spi_vif.clk)
	$rose(spi_vif.busy) |=> ##(8*SCLK_PERIOD) $fell(spi_vif.busy);
endproperty

property cs_low;
	@(negedge spi_vif.clk)
	( $rose(spi_vif.mosi) || $fell(spi_vif.mosi) ) |-> !(spi_vif.cs_n);
endproperty

property cs_deassert;
	@(negedge spi_vif.clk)
	$fell(spi_vif.cs_n) |-> ##(8*SCLK_PERIOD) $rose(spi_vif.cs_n);
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

// busy assert 1cycle after start
property busy_after_start;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $rose(spi_vif.start) |=> $rose(spi_vif.busy);
endproperty

// cs_n deassert 1cycle after start
property cs_n_after_start;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $rose(spi_vif.start) |=> $fell(spi_vif.cs_n);
endproperty

// busy deasser 1cycle after done
property busy_after_done;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $rose(spi_vif.done) |=> $fell(spi_vif.busy);
endproperty

//check sampling
property negedge_sampling;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $fell(spi_vif.sclk) |-> $changed(spi_tb.dut.rx_reg[7:0]);
endproperty

property sclk_idle_low;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  (spi_vif.cs_n) |-> (spi_vif.sclk == 1'b0);
endproperty

assert_sclk_idle_low   : assert property(sclk_idle_low);
assert_negedge_sampling: assert property(negedge_sampling) else $display( "SAMPLING_ERROR");
assert_reset  	       : assert property(reset);
assert_bus_high        : assert property(bus_high);
assert_cs_low          : assert property(cs_low);
assert_busy_deassert   : assert property(busy_deassert);
assert_cs_deassert     : assert property(cs_deassert);
assert_cs_aligned_done : assert property(cs_aligned_done);
assert_rxdata_timing   : assert property(rxdata_timing);
assert_sclk_glitch_rose: assert property(sclk_glitch_rose);
assert_sclk_glitch_fell: assert property(sclk_glitch_fell);
assert_busy_after_start: assert property(busy_after_start);
assert_cs_n_after_start: assert property(cs_n_after_start);
assert_busy_after_done : assert property(busy_after_done);
