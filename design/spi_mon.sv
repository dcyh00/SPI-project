class spi_mon extends uvm_monitor;
  `uvm_component_utils(spi_mon)

  int tran_count;
  int tran_index;
  string tran_type;
  bit [7:0] shift_reg;

  virtual spi_if.mon_mp vif;   // use mon_mp
  uvm_analysis_port #(spi_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if.mon_mp)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interface (spi_if.mon_mp) not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr_dut;


    forever begin
      @(posedge vif.clk);  // Clocking block
      tr_dut          = spi_tran::type_id::create("tr_dut");
      tr_dut.rst_n    = vif.rst_n;
      tr_dut.start    = vif.start;
      tr_dut.tx_data  = vif.tx_data;
      tr_dut.rx_data  = vif.rx_data;
      tr_dut.busy     = vif.busy;
      tr_dut.done     = vif.done;
      tr_dut.sclk     = vif.sclk;
      tr_dut.mosi     = vif.mosi;
      tr_dut.miso     = vif.miso;
      tr_dut.cs_n     = vif.cs_n;
      tr_dut.slave_rx_data = vif.slave_rx_data;
      tr_dut.slave_send_data = vif.slave_send_data;

	@(negedge vif.clk);

      mon_ap.write(tr_dut);
    end
  endtask
endclass
