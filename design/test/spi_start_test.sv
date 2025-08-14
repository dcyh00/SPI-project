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
        seq.randomize() with {cmd==0;};
        seq.start(env.agt.sqr);
      end
      begin
        repeat(20) @(posedge vif.clk);
        vif.start = 1'b1;
        repeat(10) @(posedge vif.clk);
        vif.start = 1'b0;
      end
    join

    #1000ns;
    phase.drop_objection(this);
  endtask

endclass


