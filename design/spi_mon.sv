class spi_mon extends uvm_monitor;
  `uvm_component_utils(spi_mon)

  int tran_count;
  int tran_index;
  string tran_type;

  virtual spi_if.mon_mp vif;   // use mon_mp
  uvm_analysis_port #(spi_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interface (spi_if) not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr_dut;

    @(posedge vif.clk);  // Clocking block

    forever begin
      @(posedge vif.clk);  // Clocking block
      tr_dut          = spi_tran::type_id::create("tr_dut");
      tr_dut.clk      = vif.clk;
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

      if(!uvm_config_db#(int)::get(null, "", "tran_count", tran_count)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_count from spi_drv")
      end
      if(!uvm_config_db#(int)::get(null, "", "tran_index", tran_index)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_index from spi_drv")
      end
      if(!uvm_config_db#(string)::get(null, "", "tran_type", tran_type)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_type from spi_drv")
      end

      `uvm_info("MONITOR", $sformatf("Observe %0d/%0d %s tran from DUT: tx_data=%8b | rx_dta=%8b | cs_n=%0b | mosi=%0b | miso=%0b",
                                     tran_index, tran_count, tran_type, tr_dut.tx_data, tr_dut.rx_data, tr_dut.cs_n, tr_dut.mosi, tr_dut.miso),
             UVM_MEDIUM)

      tr_dut.tran_count = this.tran_count;
      tr_dut.tran_index = this.tran_index;
      tr_dut.tran_type = this.tran_type;
      mon_ap.write(tr_dut);
    end
  endtask
endclass
