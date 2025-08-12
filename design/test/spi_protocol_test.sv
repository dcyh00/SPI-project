class spi_protocol_test extends spi_test;
  `uvm_component_utils(spi_protocol_test)

	protocol_seq seq;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    seq = protocol_seq::type_id::create("seq");

    seq.seq_count   = this.seq_count;
    seq.min_delay   = this.seq_min_delay;
    seq.max_delay   = this.seq_max_delay;


    phase.raise_objection(this);
    fork
    	seq.start(env.agt.sqr);
    join

    phase.drop_objection(this);
  endtask

endclass

