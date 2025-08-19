parameter CLK_DIV = 4;
parameter SCLK_PERIOD = 2*CLK_DIV;
//CLK_DIV == 4
bit [2:0] bit_cnt;
assign bit_cnt = spi_tb.dut.bit_cnt[2:0];
//last bit == bit_cnt == 0 && $fell(spi_clk)

property reset;
  @(posedge spi_vif.clk or negedge spi_vif.rst_n)
  (!spi_vif.rst_n) |-> (spi_vif.busy    == 0 &&
                        spi_vif.sclk    == 0 &&
                        spi_vif.cs_n    == 1 &&
                        spi_vif.done    == 0 &&
                        spi_vif.rx_data == 0
                        );
endproperty

//when there is data chg, the busy must be always HIGH
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
property cs_n_deassert; //All your tools and features are now in one
  @(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
  $fell(spi_vif.cs_n) |-> ##(8*SCLK_PERIOD) $rose(spi_vif.cs_n);
endproperty

property cs_n_deassert_done_assert;
	@(negedge spi_vif.clk) disable iff( !spi_vif.rst_n)
	$fell(spi_vif.cs_n) |-> ##(8*SCLK_PERIOD) $rose(spi_vif.done);
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
  ($rose(spi_vif.start) && !spi_vif.busy) |=> $rose(spi_vif.busy);
endproperty

// cs_n deassert 1cycle after start
property cs_n_after_start;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  ($rose(spi_vif.start) && !spi_vif.busy) |=> $fell(spi_vif.cs_n);
endproperty

// busy deassert 1cycle after done
property busy_after_done;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $rose(spi_vif.done) |=> $fell(spi_vif.busy);
endproperty

//ensure mosi only chg on posedge not negedge
property posedge_shifting;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $fell(spi_vif.sclk) |-> $stable(spi_tb.dut.mosi);
endproperty

//check sampling // add condition to prevent false assertion due to 8'hFF and 8'h00
property negedge_sampling;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  $fell(spi_vif.sclk) &&
  !((spi_tb.dut.rx_reg == 8'hFF && spi_vif.miso == 1) || (spi_tb.dut.rx_reg == 8'h00 && spi_vif.miso == 0))
  |-> $changed(spi_tb.dut.rx_reg[7:0]);
endproperty

property sclk_idle_low;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  (spi_vif.cs_n) |-> (spi_vif.sclk == 1'b0);
endproperty

// Need to run spi_start_test.sv to verify start_ignored_when_busy
// start ignored when busy
property start_ignored_when_busy;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  (spi_vif.busy && spi_vif.start) |=> $stable(spi_tb.dut.tx_reg) throughout spi_vif.busy;
endproperty

// Check lastbit
sequence last_bit;
  (spi_tb.dut.bit_cnt == 0) &&
  (spi_tb.dut.clk_cnt == 3) &&
  (!spi_vif.cs_n);
endsequence

// done 1 clk cycle after lastbit
property done_after_lastbit;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  last_bit ##CLK_DIV last_bit |=>  $rose(spi_vif.done) ##1 $fell(spi_vif.done);
endproperty

// Verify sclk 2*CLK_DIV clk period
property sclk_period;
  @(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
  ((!spi_vif.cs_n) && (!spi_vif.sclk)) |-> (!spi_vif.sclk) ##CLK_DIV (spi_vif.sclk) ##CLK_DIV (!spi_vif.sclk);
endproperty

// no changes from cs_n until done = 1
property no_tran_until_done;
	@(posedge spi_vif.clk) disable iff (!spi_vif.rst_n)
	$rose(spi_vif.cs_n) |-> ##1 (spi_vif.cs_n == 0) until (spi_vif.done == 1);
    endproperty

assert_reset  	                : assert property(reset);
assert_busy_high                : assert property(busy_high);
assert_busy_deassert            : assert property(busy_deassert);
assert_cs_n_low                 : assert property(cs_n_low);
assert_cs_n_deassert            : assert property(cs_n_deassert);
assert_cs_n_deassert_done_assert: assert property(cs_n_deassert_done_assert);
assert_cs_n_aligned_done        : assert property(cs_n_aligned_done);
assert_rxdata_timing            : assert property(rxdata_timing);
assert_sclk_glitch_rose         : assert property(sclk_glitch_rose);
assert_sclk_glitch_fell         : assert property(sclk_glitch_fell);
assert_busy_after_start         : assert property(busy_after_start);
assert_cs_n_after_start         : assert property(cs_n_after_start);
assert_busy_after_done          : assert property(busy_after_done);
assert_posedge_shifting         : assert property(posedge_shifting) else $display( "SHIFTING_ERROR");
assert_negedge_sampling         : assert property(negedge_sampling) else $display( "SAMPLING_ERROR");
assert_sclk_idle_low            : assert property(sclk_idle_low);
assert_start_ignored            : assert property(start_ignored_when_busy);
assert_done_after_lastbit       : assert property(done_after_lastbit);
assert_sclk_period              : assert property(sclk_period);
assert_no_tran_until_done 	: assert property(no_tran_until_done);
