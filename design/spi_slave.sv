    // Constants
    bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
    int slave_reset_response = SLAVE_RESET_RESPONSE;

    // Simple SPI slave model for testing
    logic [7:0] slave_rx_data;
    logic [7:0] slave_tx_data;
    logic [3:0] idle_counter;

    always @(posedge spi_vif.sclk or negedge spi_vif.rst_n or posedge spi_vif.cs_n) begin
        if (!spi_vif.rst_n) begin
            slave_rx_data <= 8'h00;
            spi_vif.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
	else if (spi_vif.cs_n) begin
            spi_vif.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;

        `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                        slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
	else begin
                // Shift in MOSI on rising edge
                slave_rx_data <= {slave_rx_data[6:0], spi_vif.mosi};

                // Update MISO immediately for next bit
                spi_vif.miso <= slave_tx_data[7];
                slave_tx_data <= {slave_tx_data[6:0], 1'b0};

		`uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                    slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
    end

    always @(posedge spi_vif.clk or negedge spi_vif.rst_n) begin
        if (!spi_vif.rst_n) begin
            idle_counter <= 5'd0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (spi_vif.cs_n) begin  // SPI idle (cs_n=1)
            if (idle_counter < 5'd7) begin
                slave_tx_data <= 8'h00;  // Drive 0 for 8 cycles
                idle_counter <= idle_counter + 1;
            end
            else begin
                slave_tx_data <= SLAVE_RESET_RESPONSE;  // Revert to default
            end
        end
        else begin  // SPI active (cs_n=0)
            idle_counter <= 5'd0;  // Reset counter
        end
    end
