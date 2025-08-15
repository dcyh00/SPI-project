module spi_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

  // Include all required files
  `include "spi_tran.sv"
  `include "spi_seq_include.sv"
  `include "spi_sqr.sv"
  `include "spi_drv.sv"
  `include "spi_mon.sv"
  `include "spi_agt.sv"
  `include "spi_scb.sv"
  `include "spi_cov.sv"
  `include "spi_env.sv"
  `include "spi_test_include.sv"
  `include "spi_slave.sv"

  spi_if spi_vif();

  spi #(.CLK_DIV(4)) dut(
    .clk(spi_vif.clk),
    .rst_n(spi_vif.rst_n),
    .start(spi_vif.start),
    .tx_data(spi_vif.tx_data),
    .rx_data(spi_vif.rx_data),
    .busy(spi_vif.busy),
    .done(spi_vif.done),
    .sclk(spi_vif.sclk),
    .mosi(spi_vif.mosi),
    .miso(spi_vif.miso),
    .cs_n(spi_vif.cs_n)
  );

  initial begin
    spi_vif.init_tb();
    forever #5 spi_vif.clk = ~spi_vif.clk;
  end

  initial begin
    ASSIGN spi_vif.slave_rx_data = slave_rx_data[7:0];
  end

  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*", "vif", spi_vif);
    uvm_config_db#(virtual spi_if.drv_mp)::set(null, "*drv*", "vif", spi_vif.drv_mp);
    uvm_config_db#(virtual spi_if.mon_mp)::set(null, "*mon*", "vif", spi_vif.mon_mp);
    uvm_config_db#(int)::set(null, "*", "slave_reset_response", slave_reset_response);

    fork
      run_test();
      begin
        repeat (1000) @(posedge spi_vif.clk);
        `uvm_error("TESTBENCH", "TEST TIMEOUT")
        $finish;
      end
    join_any
  end

  initial begin
    $fsdbDumpfile("spi_sim.fsdb");
   // $fsdbDumpSVA(0, spi_tb);
    $fsdbDumpvars(0, spi_tb);
  end

  `include "spi_assertion.sv"
endmodule
