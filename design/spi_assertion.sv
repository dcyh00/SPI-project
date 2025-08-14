parameter CLK_DIV = 4;
parameter SCLK_PERIOD = 2*CLK_DIV;
//CLK_DIV == 4

property reset;
  @(posedge spi_vif.clk or negedge spi_vif.rst_n)
  (!spi_vif.rst_n) |-> (spi_vif.busy    == 0 &&
                        spi_vif.sclk    == 0 &&
                        spi_vif.cs_n    == 1 &&
                        spi_vif.done    == 0 &&
                        spi_vif.rx_data == 0
                        );
endproperty

// when there is data chg, the busy must be always HIGH
property busy_high;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  ( $rose(spi_vif.mosi) || $fell(spi_vif.mosi) ) |-> (spi_vif.busy);
endproperty

// busy deassert after 8sclk
property busy_deassert;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  $rose(spi_vif.busy) |=> ##(8*SCLK_PERIOD) $fell(spi_vif.busy);
endproperty

// when there is data chg, the cs_n must be always LOW
property cs_n_low;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  ( $rose(spi_vif.mosi) || $fell(spi_vif.mosi) ) |-> !(spi_vif.cs_n);
endproperty

// cs_n deassert after 8sclk
property cs_n_deassert;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  $fell(spi_vif.cs_n) |-> ##(8*SCLK_PERIOD) $rose(spi_vif.cs_n);
endproperty

//cs_n rose tgt as done signal asserted
property cs_n_aligned_done;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  ( $rose(spi_vif.done) ) |-> $rose(spi_vif.cs_n);
endproperty

//data update only when done rose
property rxdata_timing;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  ($rose(spi_vif.done) ) |-> $changed(spi_vif.rx_data);
endproperty

property rxdata_timing_fell;
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  ($fell(spi_vif.done) ) |=> (spi_vif.rx_data == '0);
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

assert_reset  	        : assert property(reset);
assert_busy_high        : assert property(busy_high);
assert_busy_deassert    : assert property(busy_deassert);
assert_cs_n_low         : assert property(cs_n_low);
assert_cs_n_deassert    : assert property(cs_n_deassert);
assert_cs_n_aligned_done: assert property(cs_n_aligned_done);
assert_rxdata_timing    : assert property(rxdata_timing);
assert_sclk_glitch_rose : assert property(sclk_glitch_rose);
assert_sclk_glitch_fell : assert property(sclk_glitch_fell);
assert_busy_after_start : assert property(busy_after_start);
assert_cs_n_after_start : assert property(cs_n_after_start);
assert_busy_after_done  : assert property(busy_after_done);
assert_negedge_sampling : assert property(negedge_sampling) else $display( "SAMPLING_ERROR");
assert_sclk_idle_low    : assert property(sclk_idle_low);
