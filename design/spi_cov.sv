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
    option.comment = "THIS IS MY FA_CG COVERAGE";

//    a_cp: coverpoint tr.a {
//      option.comment = "THIS IS MY FA_CG:A_CP COVERAGE";
//      option.weight = 1;
//    }
//    b_cp: coverpoint tr.b {
//      option.comment = "THIS IS MY FA_CG:B_CP COVERAGE";
//      option.weight = 1;
//    }
//    cin_cp: coverpoint tr.cin {
//      option.comment = "THIS IS MY FA_CG:CIN_CP COVERAGE";
//      option.weight = 1;
//    }
//    sum_cp: coverpoint tr.sum {
//      option.comment = "THIS IS MY FA_CG:SUM_CP COVERAGE";
//      option.weight = 1;
//    }
//    cout_cp: coverpoint tr.cout {
//      option.comment = "THIS IS MY FA_CG:COUT_CP COVERAGE";
//      option.weight = 1;
//    }
//    abcin_cp: cross a_cp, b_cp, cin_cp;
  endgroup

  function void report_phase(uvm_phase phase);
//\    `uvm_info("COVERAGE", $sformatf("Coverage spi_cg       : %.2f%%", spi_cg.get_coverage()), UVM_NONE)
//\    `uvm_info("COVERAGE", $sformatf("Coverage a_cp        : %.2f%%", spi_cg.a_cp.get_coverage()), UVM_NONE)
//\    `uvm_info("COVERAGE", $sformatf("Coverage b_cp        : %.2f%%", spi_cg.b_cp.get_coverage()), UVM_NONE)
//\    `uvm_info("COVERAGE", $sformatf("Coverage cin_cp      : %.2f%%", spi_cg.cin_cp.get_coverage()), UVM_NONE)
//\    `uvm_info("COVERAGE", $sformatf("Coverage sum_cp      : %.2f%%", spi_cg.sum_cp.get_coverage()), UVM_NONE)
//\    `uvm_info("COVERAGE", $sformatf("Coverage cout_cp     : %.2f%%", spi_cg.cout_cp.get_coverage()), UVM_NONE)
//\    `uvm_info("COVERAGE", $sformatf("Coverage abcin_cp    : %.2f%%", spi_cg.abcin_cp.get_coverage()), UVM_NONE)
  endfunction
endclass
