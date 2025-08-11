class fa_mon extends uvm_monitor;
  `uvm_component_utils(fa_mon)

  int tran_count;
  int tran_index;
  string tran_type;

  virtual fadder_if vif;   // use mon_mp
  uvm_analysis_port #(fa_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual fadder_if)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interface (fadder_if) not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    fa_tran tr_dut;

    @(vif.mon_cb);  // Clocking block

    forever begin
      @(vif.mon_cb);  // Clocking block
      tr_dut      = fa_tran::type_id::create("tr_dut");
      tr_dut.a    = vif.mon_cb.a_tb;
      tr_dut.b    = vif.mon_cb.b_tb;
      tr_dut.cin  = vif.mon_cb.cin_tb;
      tr_dut.sum  = vif.mon_cb.sum_tb;
      tr_dut.cout = vif.mon_cb.cout_tb;

      if(!uvm_config_db#(int)::get(null, "", "tran_count", tran_count)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_count from fa_drv")
      end
      if(!uvm_config_db#(int)::get(null, "", "tran_index", tran_index)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_index from fa_drv")
      end
      if(!uvm_config_db#(string)::get(null, "", "tran_type", tran_type)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_type from fa_drv")
      end

      `uvm_info("MONITOR", $sformatf("Observe %0d/%0d %s tran from DUT: a_tb=%b, b_tb=%b, cin_tb=%b > sum_tb=%b, cout_tb=%b",
                                     tran_index, tran_count, tran_type, tr_dut.a, tr_dut.b, tr_dut.cin, tr_dut.sum, tr_dut.cout),
             UVM_MEDIUM)

      tr_dut.tran_count = this.tran_count;
      tr_dut.tran_index = this.tran_index;
      tr_dut.tran_type = this.tran_type;
      mon_ap.write(tr_dut);
    end
  endtask
endclass
