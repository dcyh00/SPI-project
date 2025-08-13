class spi_drv extends uvm_driver #(spi_tran);
  `uvm_component_utils(spi_drv)

  virtual spi_if vif;
  uvm_analysis_port #(spi_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("DRIVER", "Virtual interface (spi_if) not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr;
		vif.rst_n <= 1'b0;
		repeat(5) @(posedge vif.clk);
		vif.rst_n <= 1'b1;
		repeat(5) @(posedge vif.clk);
    forever begin
      seq_item_port.get_next_item(tr);

      if(tr.cmd == 1) begin
	      `uvm_info(get_type_name(), "CMD == 1",UVM_LOW)

		    vif.tx_data	<=	tr.tx_data;
		    vif.miso	<=	tr.miso;
	    end
	    else begin
		    tran_seq(tr);
	    end

	    seq_item_port.item_done();
    end
  endtask


  task tran_seq(spi_tran tr);
		@(vif.drv_cb);
		vif.start 	<= 1'b1;
		vif.tx_data 	<= tr.tx_data;
		vif.miso	<= tr.miso;
		@(vif.drv_cb);
		vif.start 	<= 1'b0;
		@(negedge vif.done);

	endtask
endclass

