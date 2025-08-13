class spi_cov extends uvm_component;
  `uvm_component_utils(spi_cov)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_cov) cov_imp;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cov_imp = new("cov_imp", this);
    spi_cg = new();
    spi_cg.set_inst_name($sformatf("%s\ (spi_cg\)", get_full_name()));
  endfunction

  // This will be called when transactions arrive
  function void write(spi_tran tr);
    spi_cg.sample(tr);
  endfunction

  covergroup spi_cg with function sample(spi_tran tr);
    option.per_instance = 1;
    option.weight = 1;
    option.comment = "THIS IS MY SPI_CG COVERAGE";

    RST_N_CP: coverpoint tr.rst_n {
      option.comment = "THIS IS MY_SPI_CG:RST_N_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    START_CP: coverpoint tr.start {
      option.comment = "THIS IS MY_SPI_CG:START_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    TX_DATA_CP: coverpoint tr.tx_data {
      option.comment = "THIS IS MY_SPI_CG:TX_DATA_CP COVERAGE";
      option.weight  = 1;
      bins zero     = {0};
      bins non_zero = {[8'h01:8'hFF]};
    }
    RX_DATA_CP: coverpoint tr.rx_data {
      option.comment = "THIS IS MY_SPI_CG:RX_DATA_CP COVERAGE";
      option.weight  = 1;
      bins zero     = {0};
      bins non_zero = {[8'h01:8'hFF]};
    }
    BUSY_CP: coverpoint tr.busy {
      option.comment = "THIS IS MY_SPI_CG:BUSY_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    DONE_CP: coverpoint tr.done {
      option.comment = "THIS IS MY_SPI_CG:DONE_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    SCLK_CP: coverpoint tr.sclk {
      option.comment = "THIS IS MY_SPI_CG:SCLK_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    MOSI_CP: coverpoint tr.mosi {
      option.comment = "THIS IS MY_SPI_CG:MOSI_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    MISO_CP: coverpoint tr.miso {
      option.comment = "THIS IS MY_SPI_CG:MISO_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
    CS_N_CP: coverpoint tr.cs_n {
      option.comment = "THIS IS MY_SPI_CG:CS_N_CP COVERAGE";
      option.weight  = 1;
      bins low  = {0};
      bins high = {1};
    }
  endgroup

  function void report_phase(uvm_phase phase);
    `uvm_info("COVERAGE", $sformatf("Coverage spi_cg    : %.2f%%", spi_cg.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage rst_n     : %.2f%%", spi_cg.RST_N_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage start_cp  : %.2f%%", spi_cg.START_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage tx_data_cp: %.2f%%", spi_cg.TX_DATA_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage rx_data_cp: %.2f%%", spi_cg.RX_DATA_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage busy_cp   : %.2f%%", spi_cg.BUSY_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage done_cp   : %.2f%%", spi_cg.DONE_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage sclk_cp   : %.2f%%", spi_cg.SCLK_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage mosi_cp   : %.2f%%", spi_cg.MOSI_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage miso_cp   : %.2f%%", spi_cg.MISO_CP.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage cs_n_cp   : %.2f%%", spi_cg.CS_N_CP.get_coverage()), UVM_NONE)
  endfunction
endclass
