class spi_start_test extends spi_test;
  `uvm_component_utils(spi_start_test)

	protocol_seq seq;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    seq = protocol_seq::type_id::create("seq");


    phase.raise_objection(this);

	fork

	begin
		vif.rst_n <= 1'b0;
		repeat(5) @(posedge vif.clk);

		vif.rst_n <= 1'b1;
		repeat(5) @(posedge vif.clk);

		vif.start = 1'b0;
		repeat(3) @(posedge vif.clk);//wait out of reset & stable input
		vif.start = 1'b1;
		repeat(3) @(posedge vif.clk);
		vif.start = 1'b0;
		repeat(3) @(posedge vif.clk);
		vif.start = 1'b1;
		seq.randomize() with {cmd==1; tx_data == 8'hFF;};
		seq.start(env.agt.sqr);
		repeat(10) @(posedge vif.clk);
		vif.start = 1'b0;
	end

	begin
		seq.randomize() with {cmd==1; tx_data == 8'hA5;};
		seq.start(env.agt.sqr);
	end

	join

	#1000ns;
    phase.drop_objection(this);
  endtask

endclass


