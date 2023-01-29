#include "cluster.h"
void single_cluster_simulate(Cluster * cluster) {
    while(cluster->cycle < 30) {
        cores_react(cluster);
        mem_react(cluster);
        save_current_msg_for_next_cycle(cluster);
        // PRINT("HA%d\n", cluster->program2);
        // PRINT2("hasPreviousBusmsg: %d, previousBusMsg type: %d\n", cluster->hasPreviousBusMsg, cluster->previousBusMsg.type);
        // PRINT2("Who sent message: %d, for which block: %d (0-X, 1-Y), ", cluster->previousBusMsg.sender, cluster->previousBusMsg.whichBlock);
        // PRINT("For whom: %d \n", cluster->previousBusMsg.receiver);
        update_bus_msg_for_next_cycle(cluster);
        if(cluster->program1.PC >= cluster->program1.NumInstructions && cluster->program2.PC >= cluster->program2.NumInstructions && !cluster->core1.Stalled && !cluster->core2.Stalled && !cluster->transactionInProgress)
            break;
        
        cluster->cycle++;
    }
}

void verify_TSO_properties(Cluster * cluster) {
        // IMPORTANT_ASSERT(cluster->program1.NumInstructions + 1 >= cluster->program1.PC >= cluster->program1.NumInstructions &&cluster->program2.NumInstructions + 1 >=cluster->program2.PC >=cluster->program2.NumInstructions, "finished all instructions");
    // IMPORTANT_ASSERT(cluster->program1.NumInstructions + 1 >= cluster->program1.PC >= cluster->program1.NumInstructions &&cluster->program2.NumInstructions + 1 >=cluster->program2.PC >=cluster->program2.NumInstructions, "finished all instructions");

    NONPROD_ASSERT(cluster->cycle < 30, "didn't hit cluster->program2 maximum 30");
    IMPORTANT_ASSERT(cluster->program1.NumInstructions + 1 >= cluster->program1.PC, "program 1 PC not too far beyond last instruction");
    IMPORTANT_ASSERT(cluster->program2.NumInstructions + 1 >=cluster->program2.PC, "program 2 pC not too far beyond last instruction" );
    IMPORTANT_ASSERT(!(cluster->core1.registers[1] == 0 && cluster->core2.registers[0] == 0), "Cannot happen: r1 read 0, and r0 read 0");
    IMPORTANT_ASSERT(!cluster->transactionInProgress, "cluster->transactionInProgress was kept positive when it should not be");
    IMPORTANT_ASSERT(!cluster->core1.Stalled, "core 1 have been stalled when it should not be");
    IMPORTANT_ASSERT(!cluster->core2.Stalled, "core 2 have been stalled when it should not be");
    // PRINT2("%d %d\n", cluster->program1.PC,cluster->program2.PC);
    
    IMPORTANT_ASSERT(!(cluster->core1.registers[1] == 0 && cluster->core2.registers[0] == 1), "Should fail on a non-deterministic run: legal outcome r1 (core 1's r1 loaded Y's value) = 0, r0 = 1");
    IMPORTANT_ASSERT(!(cluster->core1.registers[1] == 1 && cluster->core2.registers[0] == 0), "Should fail on a nondet check: legal out come r1 = 1, r0 = 0");
    IMPORTANT_ASSERT(!(cluster->core1.registers[1] == 1 && cluster->core2.registers[0] == 1), "Should fail on a non-det check: legal outcome r1 = 1, r0 = 1");
    // IMPORTANT_ASSERT(cluster->program1.PC >= cluster->program1.NumInstructions, "PC1 beyond last intruction?");
    // IMPORTANT_ASSERT(program2.PC >=cluster->program2.NumInstructions, "PC2 beyond last instruction?");
    // IMPORTANT_ASSERT(cluster->cache1.dataBlocks[0][0] == 1, "cache 1 correctly updated");
    // IMPORTANT_ASSERT(0, "smoke test");
    
}



int main() {
    
    
    // NONPROD_ASSERT(0, "smoke");

    //TSO litmus test
    Cluster * cluster1 = (Cluster *) malloc(sizeof(Cluster));
    
    TSO(cluster1);
    initialise_cluster(cluster1);

    single_cluster_simulate(cluster1);
    verify_TSO_properties(cluster1);


    //random reads and write
    //consistency properties being maintained
    //eg. same location, both think they havec E access: shouldn't happen
    //
    return 0;
}
