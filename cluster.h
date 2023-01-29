//simple MSI Atomic transaction+ atomic cluster->request protocol
// void NONPROD_ASSERT(int boolean_value, char * message);
// void __CPROVER_assume(int boolean_value);
int nondet();

#define MAX_INSTRUCTIONS 10
#define MAX_BLOCKS 2
#define BYTES_PER_BLOCK 2
#define NUM_CORES 2




#define IMPORTANT_ASSERT(E, M) __CPROVER_assert(E, M)
#ifdef PRODUCTION
#define NONPROD_ASSERT(E,M)
#define NONPROD_ASSUME(B)  
#define PRINT(M, VAR) 
#define PRINT2(M, VAR1, VAR2)
#define PRINT0(M)
#else
#define NONPROD_ASSUME(B) __CPROVER_assume(B)
#define NONPROD_ASSERT(E, M) __CPROVER_assert(E, M)
#define PRINT(M, VAR) printf(M, VAR)
#define PRINT2(M, VAR1, VAR2) printf(M, VAR1, VAR2)
#define PRINT0(M) printf(M)
#endif

#ifdef DEBUG_MODE
    #include<stdio.h>
    #include<stdlib.h>

    void __CPROVER_assert(int boolean_value, char * message) {
    if(boolean_value == 0){
        printf("[Assertion Failure]: %s\n",message);
        // exit(0);
    }
    }

    void __CPROVER_assume(int boolean_value) {
    if (boolean_value == 0){
        printf("assumption failed, exit\n");
        exit(0);
    }
    }

    int nondet() {
        return rand();
    }
#else  
#endif


//two cores, two programs, each with their own program counters
typedef enum {
    UndefI,
    Read,
    Write,
    Evict,
} InstructionType;

typedef enum {
    Idle,
    GetS,
    GetM,
    PutM,
    Data,
} BusEventType;

typedef enum {
    IorS,
    MMem,
    IorSD,
} MemBlockStateTypes;

typedef enum {
    Invalid,
    Shared,
    Modified,
    ISD,
    IMD,
    SMD,
} CacheBlockStateTypes;

typedef struct {
    InstructionType type;
    int val;
    int loc;
    int regNum;
} Instruction;

typedef struct {
    int PC;
    int NumInstructions;
    Instruction instructions[MAX_INSTRUCTIONS];
} Program;

typedef struct {
    int Stalled;
    Instruction pendingInstruction;
    int registers[10];
} Core;



typedef struct {
    int dataBlocks[MAX_BLOCKS][BYTES_PER_BLOCK];
    MemBlockStateTypes blockStates[MAX_BLOCKS];
} Mem;

typedef struct {
    BusEventType type;
    int payload[BYTES_PER_BLOCK];
    int receiver;
    int toMem;
    int sender;
    int whichBlock;
} Bus;

typedef struct {
    int dataBlocks[MAX_BLOCKS][BYTES_PER_BLOCK];
    CacheBlockStateTypes blockStates[MAX_BLOCKS];
    int doneOneThing;
} Cache;

typedef struct {
    Bus previousBusMsg;
    int hasPreviousBusMsg;
    Program program1, program2;
    Cache cache1, cache2;
    Core core1, core2;
    Mem llc;
    Bus snooping_bus;
    Bus response;
    Bus request;
    int isIssuingResponse;
    int isIssuingRequest;
    int transactionInProgress;
    int cycle;
} Cluster;

void core_reacts(int id, Cluster * cluster);
void initialise_cores(Cluster * cluster);

void initialise_cluster_misc(Cluster * cluster) {
    cluster->isIssuingResponse = 0;
    cluster->isIssuingRequest = 0;
    cluster->transactionInProgress = 0;
    cluster->cycle = 0;
}

void initialise_bus(Cluster * cluster) {
    cluster->snooping_bus.type = Idle;
    cluster->snooping_bus.payload[0] = 0;
    cluster->snooping_bus.payload[1] = 1;
    cluster->snooping_bus.receiver = 0;
    cluster->snooping_bus.sender = 0;
    cluster->snooping_bus.toMem = 0;
    cluster->isIssuingRequest = 0;
    cluster->isIssuingResponse = 0;
    cluster->response.type = Idle;
    cluster->request.type = Idle;

}

void TSO(Cluster * cluster) {
    cluster->program1.PC = 0;
    cluster->program1.NumInstructions = 2;
    cluster->program1.instructions[0].type = Write;
    cluster->program1.instructions[0].val = 1;
    cluster->program1.instructions[0].loc = 0;//write x
    cluster->program1.instructions[1].type = Read;
    cluster->program1.instructions[1].val = 1;
    cluster->program1.instructions[1].loc = 1;//read y
    cluster->program1.instructions[1].regNum = 1; //core 1 reads to r1

    cluster->program2.PC = 0;
    cluster->program2.NumInstructions = 2;
    cluster->program2.instructions[0].type = Write;
    cluster->program2.instructions[0].val = 1; 
    cluster->program2.instructions[0].loc = 1;//write y
    cluster->program2.instructions[1].type = Read;
    cluster->program2.instructions[1].val = 1;
    cluster->program2.instructions[1].loc = 0;//read x
    cluster->program2.instructions[1].regNum = 0; //core 2 reads to r0
}
void initialise_mem(Cluster * cluster) {
    cluster->llc.blockStates[0] = IorS;
    cluster->llc.blockStates[1] = IorS;
    cluster->llc.dataBlocks[0][0] = 0;
    cluster->llc.dataBlocks[1][0] = 0;

    //for now we only use the first byte of a block, therefore 
    //the below does not matter
    cluster->llc.dataBlocks[1][1] = 0;
    cluster->llc.dataBlocks[0][1] = 0;
}
void initialise_cache(Cluster * cluster) {
    //cache 1
    cluster->cache1.blockStates[0] = Invalid;
    cluster->cache1.blockStates[1] = Invalid;
    cluster->cache1.dataBlocks[0][0] = 99;
    cluster->cache1.dataBlocks[1][0] = 88;
    //the next 2 lines do not matter 
    cluster->cache1.dataBlocks[0][1] = 0;
    cluster->cache1.dataBlocks[1][1] = 0;
    cluster->hasPreviousBusMsg = 0;
    cluster->cache1.doneOneThing = 0;
    

    //cache 2
    cluster->cache2.blockStates[0] = Invalid;
    cluster->cache2.blockStates[1] = Invalid;
    cluster->cache2.dataBlocks[0][0] = 77;
    cluster->cache2.dataBlocks[1][0] = 66;
    //the next 2 lines do not matter 
    cluster->cache2.dataBlocks[0][1] = 0;
    cluster->cache2.dataBlocks[1][1] = 0;
    cluster->hasPreviousBusMsg = 0;
    cluster->cache2.doneOneThing = 0;


}

void initialise_cluster(Cluster * cluster) {
    initialise_cluster_misc(cluster);
    initialise_bus(cluster);
    initialise_mem(cluster);
    initialise_cache(cluster);
    initialise_cores(cluster);
}

void cache_deal_OwnGetS(int id, Cluster * cluster) {
    return; //own message, nothing to do
}

void cache_deal_OtherGetS(int id, Cluster * cluster) {
    int thisBlock;
    int requestor;
    if(id == 1) {
        thisBlock = cluster->previousBusMsg.whichBlock;
        switch (cluster->cache1.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            break; //ignore
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cluster->cache1.blockStates[thisBlock] = Shared;
            requestor = cluster->previousBusMsg.sender;
            cluster->response.type = Data;
            cluster->response.payload[0] = cluster->cache1.dataBlocks[thisBlock][0];
            cluster->response.payload[1] = cluster->cache1.dataBlocks[thisBlock][1];
            cluster->response.receiver = requestor;
            cluster->response.toMem = 1; //also write back to cache
            cluster->response.sender = id;
            cluster->response.whichBlock = thisBlock;
            cluster->isIssuingResponse =1;
            cluster->cache1.doneOneThing = 1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states when another processor is issuing coherence cluster->request");
            break;
        }
    }
    if(id == 2) {
        thisBlock = cluster->previousBusMsg.whichBlock;
        switch (cluster->cache2.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            break; //ignore
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cluster->cache2.blockStates[thisBlock] = Shared;
            requestor = cluster->previousBusMsg.sender;
            cluster->response.type = Data;
            cluster->response.payload[0] = cluster->cache2.dataBlocks[thisBlock][0];
            cluster->response.payload[1] = cluster->cache2.dataBlocks[thisBlock][1];
            cluster->response.receiver = requestor;
            cluster->response.toMem = 1; //also write back to cache
            cluster->response.sender = id;
            cluster->response.whichBlock = thisBlock;
            cluster->cache2.doneOneThing = 1;
            cluster->isIssuingResponse = 1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states");
            break;
        }
    }

}
void cache_deal_OtherGetM(int id, Cluster * cluster) {
    int thisBlock;
    
    int requestor;
    if(id == 1) {
        thisBlock = cluster->previousBusMsg.whichBlock;
        switch (cluster->cache1.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            cluster->cache1.blockStates[thisBlock] = Invalid;
            break; 
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cluster->cache1.blockStates[thisBlock] = Invalid;
            requestor = cluster->previousBusMsg.sender;
            cluster->response.type = Data;
            cluster->response.payload[0] = cluster->cache1.dataBlocks[thisBlock][0];
            cluster->response.payload[1] = cluster->cache1.dataBlocks[thisBlock][1];
            cluster->response.receiver = requestor;
            cluster->response.toMem = 0; //ownership goes to another cache
            cluster->response.sender = id;
            cluster->response.whichBlock = thisBlock;
            cluster->cache1.doneOneThing = 1;
            cluster->isIssuingResponse =1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states");
            break;
        }
    }
    if(id == 2) {
        thisBlock = cluster->previousBusMsg.whichBlock;
        switch (cluster->cache2.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            cluster->cache2.blockStates[thisBlock] = Invalid;
            break; 
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cluster->cache2.blockStates[thisBlock] = Invalid;
            requestor = cluster->previousBusMsg.sender;
            cluster->response.type = Data;
            cluster->response.payload[0] = cluster->cache2.dataBlocks[thisBlock][0];
            cluster->response.payload[1] = cluster->cache2.dataBlocks[thisBlock][1];
            cluster->response.receiver = requestor;
            cluster->response.toMem = 0; //ownership goes to another cache
            cluster->response.sender = id;
            cluster->response.whichBlock = thisBlock;
            cluster->cache2.doneOneThing = 1;
            cluster->isIssuingResponse =1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states");
            break;
        }
    }
}
void cache_deal_OwnGetM(int id, Cluster * cluster) {
    return; //ignore since my own transaction
}
void cache_deal_OwnPutM(int id, Cluster * cluster) {
    if(id == 1) {
        ;//I have sent out PutM, now follow-up with Data message
    }
}
void core_deal_with_previous_bus_msg(int id, Cluster * cluster) {
    // PRINT2("%d, %d\n", cluster->hasPreviousBusMsg, cluster->previousBusMsg.type);
    int thisBlock;
    Instruction pending;
    if(id == 1) {
        thisBlock = cluster->previousBusMsg.whichBlock;
        if(cluster->hasPreviousBusMsg){
            switch (cluster->previousBusMsg.type)
            {
            case GetS:
                if(cluster->previousBusMsg.sender == id)
                    cache_deal_OwnGetS(id, cluster);
                else 
                    cache_deal_OtherGetS(id, cluster);
                break;
            case GetM:
                if(cluster->previousBusMsg.sender == id)
                    cache_deal_OwnGetM(id, cluster);
                else
                    cache_deal_OtherGetM(id, cluster);
                break;
            case PutM:
                ; //ignore because already processed
                break;
            case Data:
                //copy data into cache
                // NONPROD_ASSERT(0, "smoke DATA Response 1");
                //PRINT("%d", )
                if(cluster->previousBusMsg.receiver != id)
                    break;
                // PRINT("smoke after break %d \n", thisBlock);
                cluster->cache1.dataBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                cluster->cache1.dataBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1];
                cluster->cache1.doneOneThing = 1;
                cluster->transactionInProgress = 0;
                cluster->core1.Stalled = 0;
                cluster->core2.Stalled = 0;
                pending = cluster->core1.pendingInstruction;
                
                switch(cluster->cache1.blockStates[thisBlock]) {
                    case ISD:
                        
                        cluster->cache1.blockStates[thisBlock] = Shared;
                        //& complete previous instruction load
                        cluster->core1.registers[pending.regNum] = cluster->cache1.dataBlocks[thisBlock][0];
                        NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                        break;
                    case IMD:
                        // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                        // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                        // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                        cluster->cache1.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cluster->cache1.dataBlocks[thisBlock][0] = pending.val;
                        // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                        break;
                    case SMD:
                        // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                        // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                        cluster->cache1.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cluster->cache1.dataBlocks[thisBlock][0] = pending.val;
                        break;
                    default:
                        NONPROD_ASSERT(0, "received data for me while in transient state");
                        break;
                }
                break;                        
            default:
                NONPROD_ASSERT(0, "unclassified msg type");
                break;
            }
        }
        //cluster->hasPreviousBusMsg = 0;
        return;
    }
    if(id == 2) {
        thisBlock = cluster->previousBusMsg.whichBlock;
        if(cluster->hasPreviousBusMsg){
            switch (cluster->previousBusMsg.type)
            {
            case GetS:
                if(cluster->previousBusMsg.sender == id)
                    cache_deal_OwnGetS(id, cluster);
                else 
                    cache_deal_OtherGetS(id, cluster);
                break;
            case GetM:
                if(cluster->previousBusMsg.sender == id)
                    cache_deal_OwnGetM(id, cluster);
                else
                    cache_deal_OtherGetM(id, cluster);
                break;
            case PutM:
                ; //ignore because already processed
                break;
            case Data:
                //copy data into cache

                // NONPROD_ASSERT(0, "smoke DATA core 2");

                if(cluster->previousBusMsg.receiver != id)
                    break;
                // NONPROD_ASSERT(0, "smoke DATA core 2 *");
                cluster->cache2.dataBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                cluster->cache2.dataBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1];
                cluster->cache2.doneOneThing = 1;
                cluster->transactionInProgress = 0;
                cluster->core1.Stalled = 0; //unstall both cores
                cluster->core2.Stalled = 0;
                pending = cluster->core2.pendingInstruction;
                switch(cluster->cache2.blockStates[thisBlock]) {
                    case ISD:
                        cluster->cache2.blockStates[thisBlock] = Shared;
                        cluster->core2.registers[pending.regNum] = cluster->cache2.dataBlocks[thisBlock][0];
                        NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                        break;
                    case IMD:
                        // NONPROD_ASSERT(0, "SMOKE IMD TO M id 2");
                        // PRINT2("block %d of cache 2 is set to %d \n", thisBlock, pending.val);
                        cluster->cache2.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cluster->cache2.dataBlocks[thisBlock][0] = pending.val;
                        break;
                    case SMD:
                        // NONPROD_ASSERT(0, "SMOKE SMD TO M id 2");
                        cluster->cache2.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cluster->cache2.dataBlocks[thisBlock][0] = pending.val;
                        break;
                    default:
                        NONPROD_ASSERT(0, "core 2 received data for me while in transient state");
                        break;
                }
                break;                        
            default:
                NONPROD_ASSERT(0, "unclassified msg type");
                break;
            }
        }
        // cluster->hasPreviousBusMsg = 0;
        return;
    }
}
void update_PC(int id, Cluster * cluster) {
    if(id == 1) {
        if (!cluster->core1.Stalled && cluster->program1.PC <= cluster->program1.NumInstructions ){
            // NONPROD_ASSERT(0, "smoke PC UPDATE");
            cluster->program1.PC++;
        }
    }
    if(id == 2) {
        if (!cluster->core2.Stalled && cluster->program2.PC <= cluster->program2.NumInstructions) {
            // NONPROD_ASSERT(0, "smoke pc update");
            cluster->program2.PC++;
        }
    }
}

int early_terminate(int id, Cluster * cluster) {
    if(id == 1) {
        return cluster->cache1.doneOneThing;
    }
    else {
        return cluster->cache2.doneOneThing;
    }
}
void compose_PutMData(int id, Cluster * cluster) {
    cluster->isIssuingResponse = 1;
    cluster->response.type = Data;
    int blockId;
    if(id == 1){
        blockId = cluster->core1.pendingInstruction.loc;
        cluster->response.payload[0] = cluster->cache1.dataBlocks[blockId][0];
        cluster->response.payload[1] = cluster->cache1.dataBlocks[blockId][1];
        cluster->response.receiver = 0; //no cores receive this data
        cluster->response.toMem = 1; //for memory
        cluster->response.sender = id;
        cluster->response.whichBlock = blockId;//TODO: needs to be updated
    }
    else {
        blockId = cluster->core2.pendingInstruction.loc;
        cluster->response.payload[0] = cluster->cache2.dataBlocks[blockId][0];
        cluster->response.payload[1] = cluster->cache2.dataBlocks[blockId][1];
        cluster->response.receiver = 0; //no cores receive this data
        cluster->response.toMem = 1; //for memory
        cluster->response.sender = id;
        cluster->response.whichBlock = blockId;//TODO: needs to be updated
    }
}
void execute_instruction(int id, Cluster * cluster) {
    Instruction instr;
    if(id == 1) {
        if(cluster->core1.Stalled || cluster->program1.PC >= cluster->program1.NumInstructions ) {
            ;//keep stalling, stalled by other cores' coherence transactions
        }
        else {//take instruction to execute
            instr = cluster->program1.instructions[cluster->program1.PC];
            switch(instr.type) {
                case Read:
                    switch (cluster->cache1.blockStates[instr.loc])
                    {
                    case Invalid:
                        
                        cluster->core1.pendingInstruction = instr;
                        if(cluster->transactionInProgress) {//disallow PC to move to next instruction
                            cluster->core1.Stalled = 1;       
                        }
                        else {
                            cluster->cache1.blockStates[instr.loc] = ISD;
                            cluster->request.type = GetS;
                            cluster->request.sender = id;
                            cluster->request.whichBlock = instr.loc;
                            cluster->isIssuingRequest = id;
                            cluster->transactionInProgress = id;
                            cluster->core1.Stalled = 1;
                        }
                        break;
                    case Shared:
                        cluster->core1.registers[instr.regNum] = cluster->cache1.dataBlocks[instr.loc][0];
                        break;
                    case Modified:
                        cluster->core1.registers[instr.regNum] = cluster->cache1.dataBlocks[instr.loc][0];
                        break;
                    default://TODO: Allow SMD to hit
                        NONPROD_ASSERT(0, "atomic transaction violated");
                        break;
                    }
                    break;
                case Write:
                    
                    switch (cluster->cache1.blockStates[instr.loc])
                    {
                    case Invalid:
                        cluster->core1.pendingInstruction = instr;
                        if(cluster->transactionInProgress) {
                            cluster->core1.Stalled = 1;
                            
                        }
                        else {
                            cluster->cache1.blockStates[instr.loc] = IMD;
                            cluster->request.type = GetM;
                            cluster->request.sender = id;
                            cluster->request.whichBlock = instr.loc;
                            cluster->isIssuingRequest = id;
                            cluster->transactionInProgress = id;
                            cluster->core1.Stalled = 1;
                        }
                        break;
                    case Shared:
                        cluster->core1.pendingInstruction = instr;
                        if(cluster->transactionInProgress) {
                            cluster->core1.Stalled = 1;
                            
                        }
                        else {
                            // NONPROD_ASSERT(0, "smoke test cluster->core1 shared no Trans in progress branch");
                            
                            cluster->cache1.blockStates[instr.loc] = SMD;
                            cluster->request.type = GetM;
                            cluster->request.sender = id;
                            cluster->request.whichBlock = instr.loc;
                            cluster->isIssuingRequest = id;
                            cluster->transactionInProgress = id;
                            cluster->core1.Stalled = 1;
                        }
                        break;
                    case Modified:
                        // NONPROD_ASSERT(0, "smoke test cluster->core1 modified no Trans in progress branch");
                        cluster->cache1.dataBlocks[instr.loc][0] = instr.val;
                        break;
                    default:
                        break;
                    }
                    break;
                case Evict:
                    cluster->core1.pendingInstruction = instr;
                    if(cluster->transactionInProgress) {
                        cluster->core1.Stalled = 1;
                    }
                    else {//issue PutM cluster->request, set cluster->transactionInProgress
                        cluster->request.type = PutM;
                        cluster->request.sender = id;
                        cluster->request.whichBlock = instr.loc;
                        cluster->isIssuingRequest = id;
                        cluster->core1.Stalled = 1;
                        cluster->transactionInProgress = id;
                        cluster->cache1.blockStates[instr.loc] = Invalid;
                    }
                    break;
                default:
                    NONPROD_ASSERT(instr.type, "undef instruction type");
                    break;
            }
        }
    }

    if(id == 2) {
        if(cluster->core2.Stalled || cluster->program2.PC >= cluster->program2.NumInstructions) {
            ;//keep stalling, stalled by other cores' coherence transactions
        }
        else {//take instruction to execute
            instr = cluster->program2.instructions[cluster->program2.PC];
            switch(instr.type) {
                case Read:
                    switch (cluster->cache2.blockStates[instr.loc])
                    {
                    case Invalid:
                        cluster->core2.pendingInstruction = instr;
                        if(cluster->transactionInProgress) {//disallow PC to move to next instruction
                            cluster->core2.Stalled = 1;
                        }
                        else {
                            cluster->cache2.blockStates[instr.loc] = ISD;
                            cluster->request.type = GetS;
                            cluster->request.sender = id;
                            cluster->request.whichBlock = instr.loc;
                            cluster->isIssuingRequest = id;
                            cluster->transactionInProgress = id;
                            cluster->core2.Stalled = 1;
                            // PRINT("cache 2 requesting %d read access \n", instr.loc);
                        }
                        break;
                    case Shared:
                        cluster->core2.registers[instr.regNum] = cluster->cache2.dataBlocks[instr.loc][0];
                        break;
                    case Modified:
                        cluster->core2.registers[instr.regNum] = cluster->cache2.dataBlocks[instr.loc][0];
                        break;
                    default://TODO: Allow SMD to hit
                        NONPROD_ASSERT(0, "atomic transaction violated");
                        break;
                    }
                    break;
                case Write:
                    // NONPROD_ASSERT(0, "smoke test for write of core 2");
                    switch (cluster->cache2.blockStates[instr.loc])
                    {
                    case Invalid:
                        cluster->core2.pendingInstruction = instr;
                        if(cluster->transactionInProgress) {
                            cluster->core2.Stalled = 1;
                        }
                        else {
                            cluster->cache2.blockStates[instr.loc] = IMD;
                            cluster->request.type = GetM;
                            cluster->request.sender = id;
                            cluster->request.whichBlock = instr.loc;
                            cluster->isIssuingRequest = id;
                            cluster->transactionInProgress = id;
                            cluster->core2.Stalled = 1;
                        }
                        break;
                    case Shared:
                        cluster->core2.pendingInstruction = instr;
                        if(cluster->transactionInProgress) {
                            cluster->core2.Stalled = 1;
                        }
                        else {
                            cluster->cache2.blockStates[instr.loc] = SMD;
                            cluster->request.type = GetM;
                            cluster->request.sender = id;
                            cluster->request.whichBlock = instr.loc;
                            cluster->isIssuingRequest = id;
                            cluster->transactionInProgress = id;
                            cluster->core2.Stalled = 1;
                        }
                        break;
                    case Modified:
                        cluster->cache2.dataBlocks[instr.loc][0] = instr.val;
                        break;
                    default:
                        break;
                    }
                    break;
                case Evict:
                    cluster->core2.pendingInstruction = instr;
                    if(cluster->transactionInProgress) {
                        cluster->core2.Stalled = 1;
                    }
                    else {//issue PutM cluster->request, set cluster->transactionInProgress
                        cluster->request.type = PutM;
                        cluster->request.sender = id;
                        cluster->request.whichBlock = instr.loc;
                        cluster->isIssuingRequest = id;
                        cluster->core2.Stalled = 1;
                        cluster->transactionInProgress = id;
                        cluster->cache2.blockStates[instr.loc] = Invalid;
                    }
                    break;
                default:
                    NONPROD_ASSERT(0, "unrecognised instruction type");
                    break;
            }
        }
    }

}
void core_reacts(int id, Cluster * cluster) {
    
    core_deal_with_previous_bus_msg(id, cluster);
    // if(early_terminate(id))
    //     return;
    if(cluster->transactionInProgress == id) {
        //myOwn transaction
        if(cluster->snooping_bus.type == PutM) { //TOCHECK: last cycle was evict
            compose_PutMData(id, cluster);
        }
    }
    else {
        execute_instruction(id, cluster);
    }
    update_PC(id, cluster);
}

#ifdef DEBUG_MODE
void cores_react(Cluster * cluster) {
    for(int i = 1; i <= NUM_CORES; i++) {
        core_reacts(i, cluster);
    }
}
#elif defined(NONDET_CHECK) //|| defined(PRODUCTION)  //exhaustive check
void cores_react(Cluster * cluster) {
    int done[NUM_CORES + 1] = {0, 0, 0};
    for(int i = 0; i < NUM_CORES; i++) {
        unsigned id = nondet();
        
        NONPROD_ASSUME(1 <= id && id <= NUM_CORES);
        NONPROD_ASSUME(!done[id]);
        // NONPROD_ASSERT(0, "SMOKE NONDET_CHECK");
       
        //printf("chosen core %d to execute\n", id + 1);
        core_reacts(id, cluster);
        done[id] = 1;
    }
}
#elif NONDET_CHECK2 //A faster exhaustive check?
void cores_react(Cluster * cluster) {
    int done[NUM_CORES + 1] = {0, 0, 0};
    for(int i = 0; i < NUM_CORES; i++) {
        unsigned id = ((unsigned) nondet() ) % 2 + 1;

        NONPROD_ASSUME(1 <= id && id <= NUM_CORES);
        NONPROD_ASSUME(!done[id]);
        core_reacts(id, cluster);
        done[id] = 1;
    }
}
#else //(normal cbmc mode) else choose one order so we check quickly
void cores_react(Cluster * cluster) {
    for(int i = 1; i <= NUM_CORES; i++) {
        core_reacts(i, cluster);
    }
}
#endif

void initialise_cores(Cluster * cluster) {
    cluster->core1.Stalled = 0;
    cluster->core2.Stalled = 0;
}

void save_current_msg_for_next_cycle(Cluster * cluster) {
    // PRINT0("saving message on bus\n");
    if(cluster->snooping_bus.type != Idle) {
        cluster->hasPreviousBusMsg = 1;
        cluster->previousBusMsg = cluster->snooping_bus;
        //NONPROD_ASSERT(cluster->previousBusMsg.type != GetM, "Data never on bus?");
    }
    else {
        cluster->hasPreviousBusMsg = 0;
        //clear bus message? Or leave it as it is?
    }
    cluster->snooping_bus.type = Idle;
}

void update_bus_msg_for_next_cycle(Cluster * cluster){
    // NONPROD_ASSERT(!(cluster->isIssuingRequest && isIssuingcluster->response), "cannot be issuing two to bus");
    if(cluster->isIssuingRequest){
        cluster->snooping_bus= cluster->request;
        cluster->isIssuingRequest = 0;
    }
    else if(cluster->isIssuingResponse){
        cluster->snooping_bus= cluster->response;
        cluster->isIssuingResponse = 0;
    }
    else {
        cluster->snooping_bus.type = Idle;
    }

}

void mem_react(Cluster * cluster) {
    int blockId;
    // PRINT("cycle %d \n", cluster->cycle);
    // PRINT2("memory react to message type %d, haspreviousbusmsg is %d\n", cluster->previousBusMsg.type, cluster->hasPreviousBusMsg);
    if(cluster->hasPreviousBusMsg) {
        // PRINT("mem is reacting to %d\n", cluster->previousBusMsg.type);
        blockId = cluster->previousBusMsg.whichBlock;
        switch(cluster->previousBusMsg.type) 
        {
        case GetS:
            switch(cluster->llc.blockStates[blockId]) 
            {
            case IorS:
                cluster->response.payload[0] = cluster->llc.dataBlocks[blockId][0];
                cluster->response.payload[1] = cluster->llc.dataBlocks[blockId][1];
                cluster->response.receiver = cluster->previousBusMsg.sender;
                cluster->response.sender = 0;
                cluster->response.toMem = 0;
                cluster->response.type = Data;
                cluster->response.whichBlock = blockId;
                cluster->isIssuingResponse =1;
                break;
            case MMem:
                // PRINT("M->IorSD on cycle %d \n", cycle);
                cluster->llc.blockStates[blockId] = IorSD;
                break;
            default: //TOTEST: should not receive GetS in IorSD
                NONPROD_ASSERT(cluster->llc.blockStates[blockId] != IorSD, "shouldn't receive GetS cluster->request while in IorSD state: expecting data");
                break;
            }
            break;
        case GetM:
            // PRINT("GetM to process with block state: %d\n", cluster->llc.blockStates[blockId]);
            switch(cluster->llc.blockStates[blockId]) 
            {
            case IorS:
                // NONPROD_ASSERT(cluster->transactionInProgress, "transaction should be in progress while llc responding with data");
                cluster->response.payload[0] = cluster->llc.dataBlocks[blockId][0];
                cluster->response.payload[1] = cluster->llc.dataBlocks[blockId][1];
                cluster->response.receiver = cluster->previousBusMsg.sender;
                cluster->response.sender = 0;
                cluster->response.toMem = 0;
                cluster->response.type = Data;
                cluster->response.whichBlock = blockId;
                cluster->isIssuingResponse =1;
                cluster->llc.blockStates[blockId] = MMem;
                break;
            case MMem:
                //PRINT("FOR a GetM cluster->request from %d for an M block, should reach here\n", cluster->previousBusMsg.sender);
                break;
            default:
                break;  
            }
            break;
        case PutM:
            cluster->llc.blockStates[blockId] = IorSD;
            break;
        case Data://TOTEST: cluster->llc.blockStates[blockId] was IorSD
            if(cluster->previousBusMsg.toMem)
            {    
                // PRINT0("this is data to mem\n");
                cluster->llc.blockStates[blockId] = IorS;
                cluster->llc.dataBlocks[blockId][0] = cluster->previousBusMsg.payload[0];
                cluster->llc.dataBlocks[blockId][1] = cluster->previousBusMsg.payload[1];
                //cluster->transactionInProgress = 0;
                cluster->core1.Stalled = 0;
                cluster->core2.Stalled = 0;
            }
            break;
        default://TOTEST: should not be idle since hasPrevious... is nonzero
            break;
        }
    }
    // cluster->hasPreviousBusMsg = 0;
}









