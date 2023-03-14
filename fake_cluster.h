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
    GetCurrent,
    PutM,
    Data,
    GO_CXL,
    
    GO_M,
    GO_E,
    GO_S,
    GO_I,
} BusEventType;


typedef struct {
    InstructionType type;
    int val;
    int loc;
    int regNum;
    int external;
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
    int External; //1->Home agent memory 0-> cluster memory
    int fromHA;
} Bus;

typedef struct {
    int dataBlocks[MAX_BLOCKS][BYTES_PER_BLOCK];
    int externalBlocks[MAX_BLOCKS][BYTES_PER_BLOCK];
    CacheBlockStateTypes blockStates[MAX_BLOCKS];
    CacheBlockStateTypes externalStates[MAX_BLOCKS];
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
    int clusterId;
} Cluster;

typedef enum {
    MESI_I,
    MESI_S,
    MESI_M,
    MESI_E,
} HABlockTypes;



typedef struct {
    HABlockTypes typeToGive;
    int CQID;
    int blockNum;
    int requestorCore;
    int requestorCluster;
    int DataArrivedBeforeGO;

} Tracker;


Tracker  cluster1Trackers[5], cluster2Trackers[5], HomeTrackers[10];
int trackersCount1, trackersCount2, trackersCountHome;


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

void TSO_single_cluster(Cluster * cluster) {
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
void initialise_program_memory(Cluster * cluster) {
    cluster->program1.PC = 0;
    cluster->program2.PC = 0;
    cluster->program1.NumInstructions = 0;
    cluster->program2.NumInstructions = 0;

}

void initialise_cluster(Cluster * cluster) {
    initialise_cluster_misc(cluster);
    initialise_bus(cluster);
    initialise_mem(cluster);
    initialise_cache(cluster);
    initialise_cores(cluster);
    initialise_program_memory(cluster);
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

int get_tracker_id(Cluster * cluster) {
    int trackerId = 8964;
    if(cluster->clusterId == 1)
    {        
        for(int i = 0; i <= trackersCount1 - 1; i++ ) {
            printf("cluster1Trackers[i].blockNum: %d ,cluster->previousBusMsg.whichBlock: %d, cluster->snooping_bus.whichBlock: %d\n", 
                cluster1Trackers[i].blockNum, cluster->previousBusMsg.whichBlock, cluster->snooping_bus.whichBlock);
            if(cluster1Trackers[i].blockNum == cluster->previousBusMsg.whichBlock) {
                trackerId = i;
                break;
            }
        }
    }
    else {
        for(int i = 0; i <= trackersCount2 - 1; i++ ) {
            if(cluster2Trackers[i].blockNum == cluster->previousBusMsg.whichBlock) {
                trackerId = i;
                break;
            }
        }
    }
    return trackerId;
}
void core_deal_with_previous_bus_msg(int id, Cluster * cluster) {
    // PRINT2("%d, %d\n", cluster->hasPreviousBusMsg, cluster->previousBusMsg.type);
    int thisBlock;
    Instruction pending;
    int trackerId;
    int clusterId = cluster->clusterId;
    thisBlock = cluster->previousBusMsg.whichBlock;
    if(id == 1) {
        if(cluster->hasPreviousBusMsg){
            if(cluster->previousBusMsg.External == 1) {
                //this message is about a communication to the HA
                printf("got previous external bus message\n");
                switch(cluster->previousBusMsg.type)
                {
                case GetS:
                    if(cluster->previousBusMsg.fromHA) {//if bus message from HA, reply with data
                        switch(cluster->cache1.externalStates[thisBlock]) {
                            case Invalid:
                                break; //ignore, i don't have a copy
                            case Shared:
                                cluster->isIssuingResponse = 1;
                                cluster->response.External = 1;
                                cluster->response.fromHA = 0;
                                cluster->response.sender = 1; //cluster 1
                                cluster->response.toMem = 0;
                                cluster->response.receiver = NUM_CORES + 1; //indicating to Host, not to other cores
                                cluster->response.whichBlock = thisBlock;
                                cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                                cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];
                                cluster->response.type = Data;

                                break;
                            case Modified:

                                cluster->isIssuingResponse = 1;
                                cluster->response.External = 1;
                                cluster->response.fromHA = 0;
                                cluster->response.sender = 1; //cluster 1
                                cluster->response.toMem = 0;
                                cluster->response.receiver = NUM_CORES + 1; //indicating to host, not for other cores
                                cluster->response.whichBlock = thisBlock;
                                cluster->cache1.externalStates[thisBlock] = Shared; //downgrade state to shared
                                cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                                cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];
                                cluster->response.type = Data;
                                
                                break;
                            default:
                                break;

                        }
                    }
                    else {//if bus message from own core, ignore. Otherwise search for the block and reply
                        if(cluster->previousBusMsg.sender == id)
                            break;//ignore
                        switch (cluster->cache1.externalStates[thisBlock])
                        {
                        case Invalid:
                            break;
                        case Shared:
                            cluster->isIssuingResponse = 1;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 1; //core 1
                            cluster->response.receiver = 2; //cluster 2 requested this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];
                            cluster->response.type = Data;

                            break;
                        case Modified:
                            cluster->response.type = Data;

                            cluster->isIssuingResponse = 1;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 1; //core 1
                            cluster->response.receiver = 2; //cluster 2 wanted this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->cache1.externalStates[thisBlock] = Shared; //downgrade state to shared
                            cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];
                            break;
                        default:
                            break;
                        }

                    }
                    break;//ignore
                case GetM:
                    if(cluster->previousBusMsg.fromHA) {//if bus message from HA, reply with data
                        switch(cluster->cache1.externalStates[thisBlock]) {
                            case Invalid:
                                break; //ignore, i don't have a copy
                            case Shared:
                                //invalidate myself, don't have to send data as I am not responsible
                                //for sending the most up-to-date copy of the data, the Host is responsible
                                cluster->cache1.externalStates[thisBlock] = Invalid;
                                // cluster->isIssuingResponse = 1;
                                // cluster->response.External = 1;
                                // cluster->response.fromHA = 0;
                                // cluster->response.sender = 1; //cluster 1
                                // cluster->response.toMem = 0;
                                // cluster->response.receiver = 0; //indicating to Host, not to other cores
                                // cluster->response.whichBlock = thisBlock;
                                // cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                                // cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];

                                break;
                            case Modified:
                                //I need to send dirty data to host, to be relayed to the
                                //requestor device
                                cluster->cache1.externalStates[thisBlock] = Invalid;
                                cluster->isIssuingResponse = 1;
                                cluster->response.External = 1;
                                cluster->response.fromHA = 0;
                                cluster->response.sender = 1; //cluster 1
                                cluster->response.toMem = 0;
                                cluster->response.receiver = NUM_CORES + 1; //indicating to host, not for other cores
                                cluster->response.whichBlock = thisBlock;
                                cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                                cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];
                                cluster->response.type = Data;
                                
                                break;
                            default:
                                break;

                        }
                    }
                    else {
                        //if bus message from within cluster, try to resolve within cluster.
                        //if message was issued from own core, ignore. 
                        //Otherwise search for the block and reply
                        if(cluster->previousBusMsg.sender == id)
                            break;//ignore
                        switch (cluster->cache1.externalStates[thisBlock])
                        {
                        case Invalid://ignore
                            break;
                        case Shared:
                            cluster->cache1.externalStates[thisBlock] = Invalid;//invalidate block
                            //also send data to requestor core

                            cluster->isIssuingResponse = 1;
                            cluster->response.type = Data;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 1; //cluster 1 sends it, meaning it was cluster 2 who requested it.
                            cluster->response.receiver = 2; //cluster 2 requested this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];

                            break;
                        case Modified:
                            cluster->isIssuingResponse = 1;
                            cluster->response.type = Data;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 1; //cluster 1
                            cluster->response.receiver = 2; //cluster 2 wanted this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->cache1.externalStates[thisBlock] = Invalid; //invalidate state
                            cluster->response.payload[0] = cluster->cache1.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache1.externalBlocks[thisBlock][1];
                            break;
                        default:
                            break;
                        }

                    }
                    break;//ignore: transaction about HA memory
                case PutM:
                    break;//ignore: transaction to HA
                case Data:
                    printf("smoke data\n");
                    trackerId = get_tracker_id(cluster);
                    //TODO: (Incorrect implementation currently)
                    //cluster 1/2 not sure, and cluster1Trackers/cluster2Trackers needs
                    //to be pinned down rather than assumed to be 1
                    
                    printf("1 trackerId is %d, dataArrivesBeforeGO is %d\n", trackerId, cluster1Trackers[trackerId].DataArrivedBeforeGO);
                    //TODO: revise the blockId part of cxl_units.h for dcoh_acts,trackerId instead of blockId


                    if(cluster->previousBusMsg.receiver != id)
                        break;
                    printf("received data logic shoule be activated after got Data for write, payload[0] is %d, payload[1] is %d\n", cluster->previousBusMsg.payload[0], cluster->previousBusMsg.payload[1]);
                    // PRINT("smoke after break %d \n", thisBlock);
                    //TODO!!!: we assume the modified byte is always the first byte, need to be variable
                    cluster->cache1.externalBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1]; 
                    if(cluster1Trackers[trackerId].DataArrivedBeforeGO == 0){//GO not arrived, needs to continue stalling
                        cluster1Trackers[trackerId].DataArrivedBeforeGO = 1; // signals to the later GO processing clause that data arrived earlier than GO, and must not overwrite
                        //copy data in, but cannot start write yet. TO CONFIRM: Read can happen already?
                        cluster->cache1.externalBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                        // switch(cluster->cache1.externalStates[thisBlock]) {
                        //     case ISD:
                        //         //& complete previous instruction load                                
                        //         cluster->core1.registers[pending.regNum] = cluster->cache1.externalBlocks[thisBlock][0];
                        //         NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                        //         break;
                        //     case IMD:
                        //         break;
                        //     case SMD:
                        //         break;
                        //     default:
                        //         NONPROD_ASSERT(0, "received data for me while in transient state");
                        //         break;
                        // }
                    }
                    else {
                        NONPROD_ASSERT(cluster1Trackers[trackerId].DataArrivedBeforeGO == 2, "If GO arrived first, DataArrivedBeforeGO should have been set to 2");                        

                        //GO arrived, complete transaction
                        cluster->cache1.doneOneThing = 1;//TODO: whether should doneOneThing be maintained for a core_reacts function call
                        cluster->transactionInProgress = 0;
                        cluster->core1.Stalled = 0;
                        cluster->core2.Stalled = 0;
                        pending = cluster->core1.pendingInstruction;
                        //TODO: make sure whether other places needs advancing PC or not
                        cluster->program1.PC++;
                        switch(cluster->cache1.externalStates[thisBlock]) {
                            case ISD:
                                cluster->cache1.externalBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                                
                                cluster->cache1.externalStates[thisBlock] = Shared;
                                //& complete previous instruction load                                
                                cluster->core1.registers[pending.regNum] = cluster->cache1.externalBlocks[thisBlock][0];
                                NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                                break;
                            case IMD:
                                // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                                // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                                cluster->cache1.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache1.externalBlocks[thisBlock][0] = pending.val;
                                // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                                break;
                            case SMD:
                                // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                                cluster->cache1.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache1.externalBlocks[thisBlock][0] = pending.val;
                                break;
                            default:
                                NONPROD_ASSERT(0, "received data for me while in transient state");
                                break;
                        }
                    }


        
                    break;
                case GO_CXL:
                    //TODO:  complete transaction: do write/read for this location
                    //copy data into cache
                    NONPROD_ASSERT(0, "smoke GO_CXL core 1");
                    trackerId = get_tracker_id(cluster);
                    printf("core 1, receiver is core %d, current executing core is %d, trackerId at GO_CXL clause: %d, trackersCount is %d, tracker is tracking block %d\n", cluster->previousBusMsg.receiver, id, trackerId, trackersCount1, cluster1Trackers[0].blockNum);
                    printf("snooping_bus block id %d, previousBusMsg block id%d\n", cluster->snooping_bus.whichBlock, cluster->previousBusMsg.whichBlock);
                    if(cluster->previousBusMsg.receiver != id){
                        break;
                    }
                    // PRINT("smoke after break %d \n", thisBlock);
                    if(cluster1Trackers[trackerId].DataArrivedBeforeGO == 1) {
                        //data arrived first, now able to complete transaction
                        cluster->cache1.doneOneThing = 1;
                        cluster->transactionInProgress = 0;
                        cluster->core1.Stalled = 0;
                        cluster->core2.Stalled = 0;
                        pending = cluster->core1.pendingInstruction;
                        
                        cluster->program1.PC++;
                        switch(cluster->cache1.externalStates[thisBlock]) {
                            case ISD:
                                
                                cluster->cache1.externalStates[thisBlock] = Shared;
                                //& complete previous instruction load
                                cluster->core1.registers[pending.regNum] = cluster->cache1.externalBlocks[thisBlock][0];
                                NONPROD_ASSERT(thisBlock == pending.loc, "GO-ISD Data block id should be the same as the read instruction's read location");
                                break;
                            case IMD:
                                // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                                // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                                cluster->cache1.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache1.externalBlocks[thisBlock][0] = pending.val;
                                // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                                break;
                            case SMD:
                                // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                                cluster->cache1.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache1.externalBlocks[thisBlock][0] = pending.val;
                                break;
                            default:
                                NONPROD_ASSERT(0, "received data for me while in transient state");
                                break;
                        }
                        printf("core 1 got a GO_CXL message\n");
                        //TODO!!!: deallocate tracker
                    }
                    else {//dataArrivesBeforeGo == 0
                        // cluster->cache1.externalBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                        // cluster->cache1.externalBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1];
                        cluster1Trackers[trackerId].DataArrivedBeforeGO = 2;//GO arrived first, data later, can't deallocate tracker
                        switch(cluster->cache1.externalStates[thisBlock]) {
                            case ISD:
                                //can't yet get out of transient state, can't read either because data is not yet available
                                NONPROD_ASSERT(thisBlock == pending.loc, "DABG Data block id should be the same as the read instruction's read location");
                                break;
                            case IMD:
                                //can already write value, but not setting state to Modified
                                cluster->cache1.externalBlocks[thisBlock][0] = pending.val;
                                // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                                break;
                            case SMD:
                                // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                                //cluster->cache1.externalStates[thisBlock] = Modified;
                                //can write value, but not setting state to Modified
                                cluster->cache1.externalBlocks[thisBlock][0] = pending.val;
                                break;
                            default:
                                NONPROD_ASSERT(0, "received data for me while in transient state");
                                break;
                        }


                    }

                    break;
                default:
                    NONPROD_ASSERT(0, "unrecognised bus message");
                    break;
                }            
                return;
            }
            //message is about memory inside cluster, not host memory, not about CXL.
            switch (cluster->previousBusMsg.type)//this part deals with internal messages
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
                        NONPROD_ASSERT(thisBlock == pending.loc, "within cluster: Data block id should be the same as the read instruction's read location");
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








    //id 2 starts
    if(id == 2) {
        if(cluster->hasPreviousBusMsg){
            if(cluster->previousBusMsg.External == 1) {
                //this message is about a communication to the HA
                printf("got previous external bus message\n");
                switch(cluster->previousBusMsg.type)
                {
                case GetS:
                    if(cluster->previousBusMsg.fromHA) {//if bus message from HA, reply with data
                        switch(cluster->cache2.externalStates[thisBlock]) {
                            case Invalid:
                                break; //ignore, i don't have a copy
                            case Shared:
                                cluster->isIssuingResponse = 1;
                                cluster->response.External = 1;
                                cluster->response.fromHA = 0;
                                cluster->response.sender = 2; //core 2
                                cluster->response.toMem = 0;
                                cluster->response.receiver = NUM_CORES + 1; //indicating to Host, not to other cores
                                cluster->response.whichBlock = thisBlock;
                                cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                                cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];
                                cluster->response.type = Data;

                                break;
                            case Modified:
                                cluster->response.type = Data;

                                cluster->isIssuingResponse = 1;
                                cluster->response.External = 1;
                                cluster->response.fromHA = 0;
                                cluster->response.sender = 2; //core 2
                                cluster->response.toMem = 0;
                                cluster->response.receiver = NUM_CORES + 1; //indicating this message is for host, not for other cores
                                cluster->response.whichBlock = thisBlock;
                                cluster->cache2.externalStates[thisBlock] = Shared; //downgrade state to shared
                                cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                                cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];
                                break;
                            default:
                                break;

                        }
                    }
                    else {//if bus message from own core, ignore. Otherwise search for the block and reply
                        if(cluster->previousBusMsg.sender == id)
                            break;//ignore
                        switch (cluster->cache2.externalStates[thisBlock])
                        {
                        case Invalid:
                            break;
                        case Shared:
                            cluster->isIssuingResponse = 1;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 2; //core 2
                            cluster->response.receiver = 1; //cluster 1 requested this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];
                            cluster->response.type = Data;

                            break;
                        case Modified:
                            cluster->isIssuingResponse = 1;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 2; //core 2
                            cluster->response.receiver = 1; //cluster 1 wanted this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->cache2.externalStates[thisBlock] = Shared; //downgrade state to shared
                            cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];
                            cluster->response.type = Data;
                            
                            break;
                        default:
                            break;
                        }

                    }
                    break;//ignore
                case GetM:
                    printf("GetM clause activated in core_deal_with_previous_bus_message\n");
                    if(cluster->previousBusMsg.fromHA) {//if bus message from HA, reply with data
                        printf("And it is from HA\n");
                        switch(cluster->cache2.externalStates[thisBlock]) {
                            case Invalid:
                                printf("MESI ---I\n");
                                break; //ignore, i don't have a copy
                            case Shared:
                                printf("MESI----S\n");
                                //invalidate myself, don't have to send data as I am not responsible
                                //for sending the most up-to-date copy of the data, the Host is responsible
                                cluster->cache2.externalStates[thisBlock] = Invalid;
                                // cluster->isIssuingResponse = 1;
                                // cluster->response.External = 1;
                                // cluster->response.fromHA = 0;
                                // cluster->response.sender = 1; //cluster 1
                                // cluster->response.toMem = 0;
                                // cluster->response.receiver = 0; //indicating to Host, not to other cores
                                // cluster->response.whichBlock = thisBlock;
                                // cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                                // cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];

                                break;
                            case Modified:
                                printf("MESI----M\n");
                                //I need to send dirty data to host, to be relayed to the
                                //requestor device
                                cluster->cache2.externalStates[thisBlock] = Invalid;
                                cluster->isIssuingResponse = 1;
                                cluster->response.External = 1;
                                cluster->response.fromHA = 0;
                                cluster->response.sender = 2; //cluster 2
                                cluster->response.toMem = 0;
                                cluster->response.receiver = NUM_CORES + 1; //indicating to host, not for other cores
                                cluster->response.whichBlock = thisBlock;
                                cluster->response.type = Data;
                                cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                                cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];
                                break;
                            default:
                                break;

                        }
                    }
                    else {//if bus message from one of own cluster's core, ignore. Otherwise search for the block and reply
                        if(cluster->previousBusMsg.sender == id)
                            break;//ignore
                        switch (cluster->cache2.externalStates[thisBlock])
                        {
                        case Invalid://ignore
                            break;
                        case Shared://TODO: when 1 core is in shared state, the other core asks GetM
                            cluster->cache2.externalStates[thisBlock] = Invalid;//invalidate block
                            //also send data to requestor core

                            cluster->isIssuingResponse = 1;
                            cluster->response.type = Data;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 2; //cluster 2 sends it, meaning it was cluster 1 who requested it.
                            cluster->response.receiver = 1; //cluster 2 requested this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];

                            break;
                        case Modified:
                            cluster->isIssuingResponse = 1;
                            cluster->response.type = Data;
                            cluster->response.External = 1;
                            cluster->response.fromHA = 0;
                            cluster->response.sender = 2; //cluster 2
                            cluster->response.receiver = 1; //cluster 2 wanted this
                            cluster->response.toMem = 0;
                            cluster->response.whichBlock = thisBlock;
                            cluster->cache2.externalStates[thisBlock] = Invalid; //invalidate state
                            cluster->response.payload[0] = cluster->cache2.externalBlocks[thisBlock][0];
                            cluster->response.payload[1] = cluster->cache2.externalBlocks[thisBlock][1];
                            break;
                        default:
                            break;
                        }

                    }
                    break;






                    break;//ignore: transaction about HA memory
                case PutM:
                    break;//ignore: transaction to HA
                case Data:
                    printf("smoke data\n");
                    trackerId = get_tracker_id(cluster);
                    printf("2 trackerId is %d, dataArrivesBeforeGO is %d\n", trackerId, cluster1Trackers[trackerId].DataArrivedBeforeGO);
                    //TODO: revise the blockId part of cxl_units.h for dcoh_acts,trackerId instead of blockId


                    if(cluster->previousBusMsg.receiver != id)
                        break;
                    printf("received data logic shoule be activated after got Data for write, payload[0] is %d, payload[1] is %d\n", cluster->previousBusMsg.payload[0], cluster->previousBusMsg.payload[1]);
                    // PRINT("smoke after break %d \n", thisBlock);
                    //TODO!!!: we assume the modified byte is always the first byte, need to be variable
                    cluster->cache2.externalBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1]; 
                    if(cluster1Trackers[trackerId].DataArrivedBeforeGO == 0){//GO not arrived, needs to continue stalling
                        cluster1Trackers[trackerId].DataArrivedBeforeGO = 1; // signals to the later GO processing clause that data arrived earlier than GO, and must not overwrite
                        //copy data in, but cannot start write yet. TO CONFIRM: Read can happen already?
                        cluster->cache2.externalBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                        // switch(cluster->cache2.externalStates[thisBlock]) {
                        //     case ISD:
                        //         //& complete previous instruction load                                
                        //         cluster->core1.registers[pending.regNum] = cluster->cache2.externalBlocks[thisBlock][0];
                        //         NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                        //         break;
                        //     case IMD:
                        //         break;
                        //     case SMD:
                        //         break;
                        //     default:
                        //         NONPROD_ASSERT(0, "received data for me while in transient state");
                        //         break;
                        // }
                    }
                    else {
                        NONPROD_ASSERT(cluster1Trackers[trackerId].DataArrivedBeforeGO == 2, "If GO arrived first, DataArrivedBeforeGO should have been set to 2");                        

                        //GO arrived, complete transaction
                        cluster->cache2.doneOneThing = 1;//TODO: whether should doneOneThing be maintained for a core_reacts function call
                        cluster->transactionInProgress = 0;
                        cluster->core1.Stalled = 0;
                        cluster->core2.Stalled = 0;
                        pending = cluster->core2.pendingInstruction;
                        //TODO: make sure whether other places needs advancing PC or not
                        cluster->program2.PC++;
                        switch(cluster->cache2.externalStates[thisBlock]) {
                            case ISD:
                                cluster->cache2.externalBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                                
                                cluster->cache2.externalStates[thisBlock] = Shared;
                                //& complete previous instruction load                                
                                cluster->core2.registers[pending.regNum] = cluster->cache2.externalBlocks[thisBlock][0];
                                NONPROD_ASSERT(thisBlock == pending.loc, "id2 ISD Data block id should be the same as the read instruction's read location");
                                break;
                            case IMD:
                                // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                                // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                                cluster->cache2.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache2.externalBlocks[thisBlock][0] = pending.val;
                                // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                                break;
                            case SMD:
                                // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                                cluster->cache2.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache2.externalBlocks[thisBlock][0] = pending.val;
                                break;
                            default:
                                NONPROD_ASSERT(0, "received data for me while in transient state");
                                break;
                        }
                    }


        
                    break;
                case GO_CXL:
                    //TODO:  complete transaction: do write/read for this location
                    //copy data into cache
                    NONPROD_ASSERT(0, "smoke GO_CXL core 1");
                    trackerId = get_tracker_id(cluster);
                    //TODO: We assume a tracker already exists, but have we made sure
                    //all dcoh_acts clauses allocate a tracker whenever an External 
                    //coherence transaction is initiated?
                    
                    printf("2 %d, %d, trackerId at GO_CXL clause: %d\n", cluster->previousBusMsg.receiver, id, trackerId);
                    if(cluster->previousBusMsg.receiver != id){
                        break;
                    }
                    // PRINT("smoke after break %d \n", thisBlock);
                    if(cluster1Trackers[trackerId].DataArrivedBeforeGO == 1) {
                        //data arrived first, now able to complete transaction
                        cluster->cache2.doneOneThing = 1;
                        cluster->transactionInProgress = 0;
                        cluster->core1.Stalled = 0;
                        cluster->core2.Stalled = 0;
                        pending = cluster->core2.pendingInstruction;
                        
                        cluster->program2.PC++;
                        switch(cluster->cache2.externalStates[thisBlock]) {
                            case ISD:
                                
                                cluster->cache2.externalStates[thisBlock] = Shared;
                                //& complete previous instruction load
                                cluster->core2.registers[pending.regNum] = cluster->cache2.externalBlocks[thisBlock][0];
                                NONPROD_ASSERT(thisBlock == pending.loc, "id 2 DABG Data block id should be the same as the read instruction's read location");
                                break;
                            case IMD:
                                // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                                // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                                cluster->cache2.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache2.externalBlocks[thisBlock][0] = pending.val;
                                // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                                break;
                            case SMD:
                                // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                                cluster->cache2.externalStates[thisBlock] = Modified;
                                //& complete previous instruction store
                                cluster->cache2.externalBlocks[thisBlock][0] = pending.val;
                                break;
                            default:
                                NONPROD_ASSERT(0, "received data for me while in transient state");
                                break;
                        }
                        printf("core 1 got a GO_CXL message\n");
                        //TODO!!!: deallocate tracker
                    }
                    else {//dataArrivesBeforeGo == 0
                        // cluster->cache2.externalBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                        // cluster->cache2.externalBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1];
                        cluster1Trackers[trackerId].DataArrivedBeforeGO = 2;//GO arrived first, data later, can't deallocate tracker
                        switch(cluster->cache2.externalStates[thisBlock]) {
                            case ISD:
                                //can't yet get out of transient state, can't read either because data is not yet available
                                NONPROD_ASSERT(thisBlock == pending.loc, "id 2 DABG = 0 Data block id should be the same as the read instruction's read location");
                                break;
                            case IMD:
                                //can already write value, but not setting state to Modified
                                cluster->cache2.externalBlocks[thisBlock][0] = pending.val;
                                // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                                break;
                            case SMD:
                                // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                                // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                                //cluster->cache2.externalStates[thisBlock] = Modified;
                                //can write value, but not setting state to Modified
                                cluster->cache2.externalBlocks[thisBlock][0] = pending.val;
                                break;
                            default:
                                NONPROD_ASSERT(0, "received data for me while in transient state");
                                break;
                        }


                    }

                    break;
                default:
                    NONPROD_ASSERT(0, "unrecognised bus message");
                    break;
                }            
                return;
            }
            switch (cluster->previousBusMsg.type)//this part deals with internal messages
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
                cluster->cache2.dataBlocks[thisBlock][0] = cluster->previousBusMsg.payload[0];
                cluster->cache2.dataBlocks[thisBlock][1] = cluster->previousBusMsg.payload[1];
                cluster->cache2.doneOneThing = 1;
                cluster->transactionInProgress = 0;
                cluster->core1.Stalled = 0;
                cluster->core2.Stalled = 0;
                pending = cluster->core2.pendingInstruction;
                
                switch(cluster->cache2.blockStates[thisBlock]) {
                    case ISD:
                        
                        cluster->cache2.blockStates[thisBlock] = Shared;
                        //& complete previous instruction load
                        cluster->core2.registers[pending.regNum] = cluster->cache2.dataBlocks[thisBlock][0];
                        printf("%d, %d, %d, %d\n", thisBlock, pending.loc, pending.type, pending.regNum);
                        NONPROD_ASSERT(thisBlock == pending.loc, "id2 within cluster Data block id should be the same as the read instruction's read location");
                        break;
                    case IMD:
                        // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                        // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                        // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                        cluster->cache2.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cluster->cache2.dataBlocks[thisBlock][0] = pending.val;
                        // PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                        break;
                    case SMD:
                        // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                        // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                        cluster->cache2.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cluster->cache2.dataBlocks[thisBlock][0] = pending.val;
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





}
void update_PC(int id, Cluster * cluster) {
    if(id == 1) {
        if (!cluster->core1.Stalled && cluster->program1.PC <= cluster->program1.NumInstructions ){
            NONPROD_ASSERT(0, "smoke PC UPDATE");
            cluster->program1.PC++;
        }
    }
    if(id == 2) {
        if (!cluster->core2.Stalled && cluster->program2.PC <= cluster->program2.NumInstructions) {
            NONPROD_ASSERT(0, "smoke pc update");
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
            printf("executing core %d's instruction %d, but got stalled at this cycle,,,%d, %d %d\n", id, cluster->program1.PC, cluster->core1.Stalled, cluster->program1.PC, cluster->program1.NumInstructions);

            ;//keep stalling, stalled by other cores' coherence transactions
        }
        else {//take instruction to execute
            printf("ffff:%d, %d\n", id, cluster->program1.PC);

            instr = cluster->program1.instructions[cluster->program1.PC];
            if(!instr.external) {
                switch(instr.type) {
                    case Read:
                        printf("instruction is read\n");
                        switch (cluster->cache1.blockStates[instr.loc])
                        {
                        case Invalid:
                            
                            cluster->core1.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {//disallow PC to move to next instruction
                                cluster->core1.Stalled = 1;       
                            }
                            else {
                                cluster->request.type = GetS;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core1.Stalled = 1;
                                cluster->cache1.blockStates[instr.loc] = ISD;
                                
                                
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
                        printf("instruction is write\n");
                        
                        switch (cluster->cache1.blockStates[instr.loc])
                        {
                        case Invalid:
                            printf("invalid case activated\n");
                            cluster->core1.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {
                                cluster->core1.Stalled = 1;
                                
                            }
                            else {
                                printf("started a transaction\n");
                                cluster->cache1.blockStates[instr.loc] = IMD;
                                cluster->request.type = GetM;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
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
                                
                                cluster->cache1.blockStates[instr.loc] = SMD;
                                cluster->request.type = GetM;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
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
                            cluster->request.External = instr.external;
                            cluster->request.fromHA = 0;
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
            
            else{
                switch(instr.type) {
                    case Read:
                        printf("instruction is read\n");
                        switch (cluster->cache1.blockStates[instr.loc])
                        {
                        case Invalid:
                            
                            cluster->core1.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {//disallow PC to move to next instruction
                                cluster->core1.Stalled = 1;       
                            }
                            else {
                                cluster->request.type = GetS;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core1.Stalled = 1;
                                if(instr.external) {
                                    cluster->cache1.externalStates[instr.loc] = ISD;
                                }
                                else {
                                    cluster->cache1.blockStates[instr.loc] = ISD;
                                }
                            }
                            break;
                        case Shared:
                            if(instr.external)
                                cluster->core1.registers[instr.regNum] = cluster->cache1.externalBlocks[instr.loc][0];
                            else
                                cluster->core1.registers[instr.regNum] = cluster->cache1.dataBlocks[instr.loc][0];
                            break;
                        case Modified:
                            if(instr.external)
                                cluster->core1.registers[instr.regNum] = cluster->cache1.externalBlocks[instr.loc][0];
                            else
                                cluster->core1.registers[instr.regNum] = cluster->cache1.dataBlocks[instr.loc][0];
                            break;
                        default://TODO: Allow SMD to hit
                            NONPROD_ASSERT(0, "atomic transaction violated");
                            break;
                        }
                        break;
                    case Write:
                        printf("instruction is write(external)\n");
                        
                        switch (cluster->cache1.blockStates[instr.loc])
                        {
                        case Invalid:
                            cluster->core1.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {
                                cluster->core1.Stalled = 1;
                                
                            }
                            else {
                                if(instr.external)
                                {
                                    printf("core 1 external write should trigger this\n");
                                    cluster->cache1.externalStates[instr.loc] = IMD;

                                }
                                else 
                                    cluster->cache1.blockStates[instr.loc] = IMD;
                                cluster->request.type = GetM;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
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
                                if(instr.external) {
                                    cluster->cache1.externalStates[instr.loc] = SMD;
                                }
                                else
                                    cluster->cache1.blockStates[instr.loc] = SMD;
                                cluster->request.type = GetM;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core1.Stalled = 1;
                            }
                            break;
                        case Modified:
                            NONPROD_ASSERT(0, "smoke test cluster->core1 modified no Trans in progress branch");
                            if(instr.external)
                                cluster->cache1.externalBlocks[instr.loc][0] = instr.val;
                            else
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
                            cluster->request.External = instr.external;
                            cluster->request.fromHA = 0;
                            cluster->isIssuingRequest = id;
                            cluster->core1.Stalled = 1;
                            cluster->transactionInProgress = id;
                            if(instr.external)
                                cluster->cache1.externalStates[instr.loc] = Invalid;
                            else
                                cluster->cache1.blockStates[instr.loc] = Invalid;
                        }
                        break;
                    default:
                        NONPROD_ASSERT(instr.type, "undef instruction type");
                        break;
                }
            }





        }
    }

    if(id == 2) {
        if(cluster->core2.Stalled || cluster->program2.PC >= cluster->program2.NumInstructions) {
            ;//keep stalling, stalled by other cores' coherence transactions
        }
        else {//take instruction to execute
            instr = cluster->program2.instructions[cluster->program2.PC];
            if(!instr.external) {
                switch(instr.type) {
                    case Read:
                        printf("instruction is read\n");
                        switch (cluster->cache2.blockStates[instr.loc])
                        {
                        case Invalid:
                            
                            cluster->core2.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {//disallow PC to move to next instruction
                                cluster->core2.Stalled = 1;       
                            }
                            else {
                                cluster->request.type = GetS;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core2.Stalled = 1;
                                cluster->cache2.blockStates[instr.loc] = ISD;
                                
                                
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
                        printf("instruction is write\n");
                        
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
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
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
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core2.Stalled = 1;
                            }
                            break;
                        case Modified:
                            // NONPROD_ASSERT(0, "smoke test cluster->core2 modified no Trans in progress branch");
                            
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
                            cluster->request.External = instr.external;
                            cluster->request.fromHA = 0;
                            cluster->isIssuingRequest = id;
                            cluster->core2.Stalled = 1;
                            cluster->transactionInProgress = id;
                            
                            cluster->cache2.blockStates[instr.loc] = Invalid;
                        }
                        break;
                    default:
                        NONPROD_ASSERT(instr.type, "undef instruction type");
                        break;
                }
            }
            
            else{
                switch(instr.type) {
                    case Read:
                        printf("instruction is read\n");
                        switch (cluster->cache2.blockStates[instr.loc])
                        {
                        case Invalid:
                            
                            cluster->core2.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {//disallow PC to move to next instruction
                                cluster->core2.Stalled = 1;       
                            }
                            else {
                                cluster->request.type = GetS;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core2.Stalled = 1;
                                if(instr.external) {
                                    cluster->cache2.externalStates[instr.loc] = ISD;
                                }
                                else {
                                    cluster->cache2.blockStates[instr.loc] = ISD;
                                }
                            }
                            break;
                        case Shared:
                            if(instr.external)
                                cluster->core2.registers[instr.regNum] = cluster->cache2.externalBlocks[instr.loc][0];
                            else
                                cluster->core2.registers[instr.regNum] = cluster->cache2.dataBlocks[instr.loc][0];
                            break;
                        case Modified:
                            if(instr.external)
                                cluster->core2.registers[instr.regNum] = cluster->cache2.externalBlocks[instr.loc][0];
                            else
                                cluster->core2.registers[instr.regNum] = cluster->cache2.dataBlocks[instr.loc][0];
                            break;
                        default://TODO: Allow SMD to hit
                            NONPROD_ASSERT(0, "atomic transaction violated");
                            break;
                        }
                        break;
                    case Write:
                        printf("instruction is write\n");
                        
                        switch (cluster->cache2.blockStates[instr.loc])
                        {
                        case Invalid:
                            cluster->core2.pendingInstruction = instr;
                            if(cluster->transactionInProgress) {
                                cluster->core2.Stalled = 1;
                                
                            }
                            else {
                                if(instr.external)
                                {
                                    printf("core 1 external write should trigger this\n");
                                    cluster->cache2.externalStates[instr.loc] = IMD;

                                }
                                else 
                                    cluster->cache2.blockStates[instr.loc] = IMD;
                                cluster->request.type = GetM;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
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
                                // NONPROD_ASSERT(0, "smoke test cluster->core2 shared no Trans in progress branch");
                                if(instr.external) {
                                    cluster->cache2.externalStates[instr.loc] = SMD;
                                }
                                else
                                    cluster->cache2.blockStates[instr.loc] = SMD;
                                cluster->request.type = GetM;
                                cluster->request.sender = id;
                                cluster->request.whichBlock = instr.loc;
                                cluster->request.External = instr.external;
                                cluster->request.fromHA = 0;
                                cluster->isIssuingRequest = id;
                                cluster->transactionInProgress = id;
                                cluster->core2.Stalled = 1;
                            }
                            break;
                        case Modified:
                            // NONPROD_ASSERT(0, "smoke test cluster->core2 modified no Trans in progress branch");
                            if(instr.external)
                                cluster->cache2.externalBlocks[instr.loc][0] = instr.val;
                            else
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
                            cluster->request.External = instr.external;
                            cluster->request.fromHA = 0;
                            cluster->isIssuingRequest = id;
                            cluster->core2.Stalled = 1;
                            cluster->transactionInProgress = id;
                            if(instr.external)
                                cluster->cache2.externalStates[instr.loc] = Invalid;
                            else
                                cluster->cache2.blockStates[instr.loc] = Invalid;
                        }
                        break;
                    default:
                        NONPROD_ASSERT(instr.type, "undef instruction type");
                        break;
                }
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
        //TODO: might want to skip executing new instructions if core_deal_with_previous_bus_msg had just completed a pending instruction?
        //TODO: execute_instructions has places where blocks needs to be changed to external
        // printf("executing instructions at all?? %d, cluster addr: %d\n", id, cluster);
        // printf("%d, %d\n", cluster->program1.PC, cluster->program1.NumInstructions);
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
        printf("cluster issuing request, fromHA: %d, External %d\n", cluster->request.fromHA, cluster->request.External);
        cluster->snooping_bus= cluster->request;
        cluster->isIssuingRequest = 0;
    }
    else if(cluster->isIssuingResponse){
        //printf("cluster got response from HA: %d, put on bus (external: %d) \n", cluster->response.fromHA, cluster->response.External);
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
        if(cluster->previousBusMsg.External) {
            return; //ignore messages about external 
        }
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

void single_cluster_simulate(Cluster * cluster) {
    while(cluster->cycle < 30) {
        cores_react(cluster);
        mem_react(cluster);
        save_current_msg_for_next_cycle(cluster);
        update_bus_msg_for_next_cycle(cluster);
        cluster->cycle++;
        if(cluster->program1.PC >= cluster->program1.NumInstructions && cluster->program2.PC >= cluster->program2.NumInstructions && !cluster->core1.Stalled && !cluster->core2.Stalled && !cluster->transactionInProgress)
            break;
        
    }
}




//adds an instruction to program memory: assumes correct NumInstructions for existing instructions
void fill_program(Cluster * cluster, Instruction * instr, int coreId) {
    if(coreId == 1) {   
        printf("printing core 1 program fill\n");
        cluster->program1.instructions[cluster->program1.NumInstructions].type = instr->type;
        cluster->program1.instructions[cluster->program1.NumInstructions].val = instr->val;
        cluster->program1.instructions[cluster->program1.NumInstructions].loc = instr->loc;
        cluster->program1.instructions[cluster->program1.NumInstructions].regNum = instr->regNum;
        cluster->program1.instructions[cluster->program1.NumInstructions].external = instr->external;
        cluster->program1.NumInstructions++;
    }
    if(coreId == 2) {
        printf("printing core 2 program fill\n");
        cluster->program2.instructions[cluster->program2.NumInstructions].type = instr->type;
        cluster->program2.instructions[cluster->program2.NumInstructions].val = instr->val;
        cluster->program2.instructions[cluster->program2.NumInstructions].loc = instr->loc;
        cluster->program2.instructions[cluster->program2.NumInstructions].regNum = instr->regNum;
        cluster->program2.instructions[cluster->program2.NumInstructions].external = instr->external;
        cluster->program2.NumInstructions++;
    }
}

Instruction * create_instruction(int external, 
                                InstructionType type, 
                                int loc, 
                                int val, 
                                int regNum) {
    Instruction * i = (Instruction * ) malloc (sizeof(Instruction));
    i->loc = loc;
    i->type = type;
    i->val = val;
    i->regNum = regNum;
    i->external = external;
    return i;
}






