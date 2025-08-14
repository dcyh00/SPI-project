class spi_protocol_test extends spi_test;
  `uvm_component_utils(spi_protocol_test)

	protocol_seq seq;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    seq = protocol_seq::type_id::create("seq");

    phase.raise_objection(this);

    seq.randomize() with { cmd==0; tx_data == 8'hA5;};
    seq.start(env.agt.sqr);

    for(int i = 0; i<10; i++) begin
      seq.randomize() with {cmd==0;};
      seq.start(env.agt.sqr);
    end

    #1000ns;
    phase.drop_objection(this);
  endtask

endclass

