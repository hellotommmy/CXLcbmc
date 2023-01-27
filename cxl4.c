//simple MSI Atomic transaction+ atomic request protocol
// void NONPROD_ASSERT(int boolean_value, char * message);
// void __CPROVER_assume(int boolean_value);
int nondet();
void core_reacts(int id);

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

Bus previousBusMsg;
int hasPreviousBusMsg;
Program program1, program2;
Cache cache1, cache2;
Core core1, core2;
Mem llc;
Bus snooping_bus;
Bus response;
int isIssuingResponse = 0;
Bus request;
int isIssuingRequest = 0;
int cycle = 0;
int transactionInProgress = 0;

void initialise_bus() {
    snooping_bus.type = Idle;
    snooping_bus.payload[0] = 0;
    snooping_bus.payload[1] = 1;
    snooping_bus.receiver = 0;
    snooping_bus.sender = 0;
    snooping_bus.toMem = 0;
    isIssuingRequest = 0;
    isIssuingResponse = 0;
    response.type = Idle;
    request.type = Idle;
}

void TSO() {
    program1.PC = 0;
    program1.NumInstructions = 2;
    program1.instructions[0].type = Write;
    program1.instructions[0].val = 1;
    program1.instructions[0].loc = 0;//write x
    program1.instructions[1].type = Read;
    program1.instructions[1].val = 1;
    program1.instructions[1].loc = 1;//read y
    program1.instructions[1].regNum = 1; //core 1 reads to r1

    program2.PC = 0;
    program2.NumInstructions = 2;
    program2.instructions[0].type = Write;
    program2.instructions[0].val = 1; 
    program2.instructions[0].loc = 1;//write y
    program2.instructions[1].type = Read;
    program2.instructions[1].val = 1;
    program2.instructions[1].loc = 0;//read x
    program2.instructions[1].regNum = 0; //core 2 reads to r0
}
void initialise_mem() {
    llc.blockStates[0] = IorS;
    llc.blockStates[1] = IorS;
    llc.dataBlocks[0][0] = 0;
    llc.dataBlocks[1][0] = 0;

    //for now we only use the first byte of a block, therefore 
    //the below does not matter
    llc.dataBlocks[1][1] = 0;
    llc.dataBlocks[0][1] = 0;
}
void initialise_cache() {
    //cache 1
    cache1.blockStates[0] = Invalid;
    cache1.blockStates[1] = Invalid;
    cache1.dataBlocks[0][0] = 99;
    cache1.dataBlocks[1][0] = 88;
    //the next 2 lines do not matter 
    cache1.dataBlocks[0][1] = 0;
    cache1.dataBlocks[1][1] = 0;
    hasPreviousBusMsg = 0;
    cache1.doneOneThing = 0;
    

    //cache 2
    cache2.blockStates[0] = Invalid;
    cache2.blockStates[1] = Invalid;
    cache2.dataBlocks[0][0] = 77;
    cache2.dataBlocks[1][0] = 66;
    //the next 2 lines do not matter 
    cache2.dataBlocks[0][1] = 0;
    cache2.dataBlocks[1][1] = 0;
    hasPreviousBusMsg = 0;
    cache2.doneOneThing = 0;


}



void cache_deal_OwnGetS(int id) {
    return; //own message, nothing to do
}

void cache_deal_OtherGetS(int id) {
    int thisBlock;
    int requestor;
    if(id == 1) {
        thisBlock = previousBusMsg.whichBlock;
        switch (cache1.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            break; //ignore
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cache1.blockStates[thisBlock] = Shared;
            requestor = previousBusMsg.sender;
            response.type = Data;
            response.payload[0] = cache1.dataBlocks[thisBlock][0];
            response.payload[1] = cache1.dataBlocks[thisBlock][1];
            response.receiver = requestor;
            response.toMem = 1; //also write back to cache
            response.sender = id;
            response.whichBlock = thisBlock;
            isIssuingResponse = 1;
            cache1.doneOneThing = 1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states when another processor is issuing coherence request");
            break;
        }
    }
    if(id == 2) {
        thisBlock = previousBusMsg.whichBlock;
        switch (cache2.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            break; //ignore
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cache2.blockStates[thisBlock] = Shared;
            requestor = previousBusMsg.sender;
            response.type = Data;
            response.payload[0] = cache2.dataBlocks[thisBlock][0];
            response.payload[1] = cache2.dataBlocks[thisBlock][1];
            response.receiver = requestor;
            response.toMem = 1; //also write back to cache
            response.sender = id;
            response.whichBlock = thisBlock;
            cache2.doneOneThing = 1;
            isIssuingResponse = 1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states");
            break;
        }
    }

}
void cache_deal_OtherGetM(int id) {
    int thisBlock;
    
    int requestor;
    if(id == 1) {
        thisBlock = previousBusMsg.whichBlock;
        switch (cache1.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            cache1.blockStates[thisBlock] = Invalid;
            break; 
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cache1.blockStates[thisBlock] = Invalid;
            requestor = previousBusMsg.sender;
            response.type = Data;
            response.payload[0] = cache1.dataBlocks[thisBlock][0];
            response.payload[1] = cache1.dataBlocks[thisBlock][1];
            response.receiver = requestor;
            response.toMem = 0; //ownership goes to another cache
            response.sender = id;
            response.whichBlock = thisBlock;
            cache1.doneOneThing = 1;
            isIssuingResponse = 1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states");
            break;
        }
    }
    if(id == 2) {
        thisBlock = previousBusMsg.whichBlock;
        switch (cache2.blockStates[thisBlock])
        {
        case Invalid:
            //ignore
            break;
        case Shared:
            cache2.blockStates[thisBlock] = Invalid;
            break; 
        case Modified:
            //downgrade to shared state, send data to requestor and mem
            cache2.blockStates[thisBlock] = Invalid;
            requestor = previousBusMsg.sender;
            response.type = Data;
            response.payload[0] = cache2.dataBlocks[thisBlock][0];
            response.payload[1] = cache2.dataBlocks[thisBlock][1];
            response.receiver = requestor;
            response.toMem = 0; //ownership goes to another cache
            response.sender = id;
            response.whichBlock = thisBlock;
            cache2.doneOneThing = 1;
            isIssuingResponse = 1;
            break;
        default:
            NONPROD_ASSERT(0, "AT, should never be in transient states");
            break;
        }
    }
}
void cache_deal_OwnGetM(int id) {
    return; //ignore since my own transaction
}
void cache_deal_OwnPutM(int id) {
    if(id == 1) {
        ;//I have sent out PutM, now follow-up with Data message
    }
}
void core_deal_with_previous_bus_msg(int id) {
    PRINT2("%d, %d\n", hasPreviousBusMsg, previousBusMsg.type);
    int thisBlock;
    Instruction pending;
    if(id == 1) {
        thisBlock = previousBusMsg.whichBlock;
        if(hasPreviousBusMsg){
            switch (previousBusMsg.type)
            {
            case GetS:
                if(previousBusMsg.sender == id)
                    cache_deal_OwnGetS(id);
                else 
                    cache_deal_OtherGetS(id);
                break;
            case GetM:
                if(previousBusMsg.sender == id)
                    cache_deal_OwnGetM(id);
                else
                    cache_deal_OtherGetM(id);
                break;
            case PutM:
                ; //ignore because already processed
                break;
            case Data:
                //copy data into cache
                // NONPROD_ASSERT(0, "smoke DATA Response 1");
                //PRINT("%d", )
                if(previousBusMsg.receiver != id)
                    break;
                PRINT("smoke after break %d \n", thisBlock);
                cache1.dataBlocks[thisBlock][0] = previousBusMsg.payload[0];
                cache1.dataBlocks[thisBlock][1] = previousBusMsg.payload[1];
                cache1.doneOneThing = 1;
                transactionInProgress = 0;
                core1.Stalled = 0;
                core2.Stalled = 0;
                pending = core1.pendingInstruction;
                
                switch(cache1.blockStates[thisBlock]) {
                    case ISD:
                        
                        cache1.blockStates[thisBlock] = Shared;
                        //& complete previous instruction load
                        core1.registers[pending.regNum] = cache1.dataBlocks[thisBlock][0];
                        NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                        break;
                    case IMD:
                        // NONPROD_ASSERT(0, "SMOKE IMD TO M id 1");
                        // NONPROD_ASSERT(thisBlock == pending.loc, "IMD: data block should be same as write loc");
                        // NONPROD_ASSERT(pending.type == Write, "should be write for IMD to M");
                        cache1.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cache1.dataBlocks[thisBlock][0] = pending.val;
                        PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                        break;
                    case SMD:
                        // NONPROD_ASSERT(0, "SMOKE SMD TO M id 1");
                        // NONPROD_ASSERT(thisBlock == pending.loc, "SMD: data block should be same as write loc");
                        cache1.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cache1.dataBlocks[thisBlock][0] = pending.val;
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
        //hasPreviousBusMsg = 0;
        return;
    }
    if(id == 2) {
        thisBlock = previousBusMsg.whichBlock;
        if(hasPreviousBusMsg){
            switch (previousBusMsg.type)
            {
            case GetS:
                if(previousBusMsg.sender == id)
                    cache_deal_OwnGetS(id);
                else 
                    cache_deal_OtherGetS(id);
                break;
            case GetM:
                if(previousBusMsg.sender == id)
                    cache_deal_OwnGetM(id);
                else
                    cache_deal_OtherGetM(id);
                break;
            case PutM:
                ; //ignore because already processed
                break;
            case Data:
                //copy data into cache

                // NONPROD_ASSERT(0, "smoke DATA core 2");

                if(previousBusMsg.receiver != id)
                    break;
                // NONPROD_ASSERT(0, "smoke DATA core 2 *");
                cache2.dataBlocks[thisBlock][0] = previousBusMsg.payload[0];
                cache2.dataBlocks[thisBlock][1] = previousBusMsg.payload[1];
                cache2.doneOneThing = 1;
                transactionInProgress = 0;
                core1.Stalled = 0; //unstall both cores
                core2.Stalled = 0;
                pending = core2.pendingInstruction;
                switch(cache2.blockStates[thisBlock]) {
                    case ISD:
                        cache2.blockStates[thisBlock] = Shared;
                        core2.registers[pending.regNum] = cache2.dataBlocks[thisBlock][0];
                        NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                        break;
                    case IMD:
                        // NONPROD_ASSERT(0, "SMOKE IMD TO M id 2");
                        PRINT2("block %d of cache 2 is set to %d \n", thisBlock, pending.val);
                        cache2.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cache2.dataBlocks[thisBlock][0] = pending.val;
                        break;
                    case SMD:
                        // NONPROD_ASSERT(0, "SMOKE SMD TO M id 2");
                        cache2.blockStates[thisBlock] = Modified;
                        //& complete previous instruction store
                        cache2.dataBlocks[thisBlock][0] = pending.val;
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
        // hasPreviousBusMsg = 0;
        return;
    }
}
void update_PC(int id) {
    if(id == 1) {
        if (!core1.Stalled && program1.PC <= program1.NumInstructions ){
            // NONPROD_ASSERT(0, "smoke PC UPDATE");
            program1.PC++;
        }
    }
    if(id == 2) {
        if (!core2.Stalled && program2.PC <= program2.NumInstructions) {
            // NONPROD_ASSERT(0, "smoke pc update");
            program2.PC++;
        }
    }
}

int early_terminate(int id) {
    if(id == 1) {
        return cache1.doneOneThing;
    }
    else {
        return cache2.doneOneThing;
    }
}
void compose_PutMData(int id) {
    isIssuingResponse = 1;
    response.type = Data;
    int blockId;
    if(id == 1){
        blockId = core1.pendingInstruction.loc;
        response.payload[0] = cache1.dataBlocks[blockId][0];
        response.payload[1] = cache1.dataBlocks[blockId][1];
        response.receiver = 0; //no cores receive this data
        response.toMem = 1; //for memory
        response.sender = id;
        response.whichBlock = blockId;//TODO: needs to be updated
    }
    else {
        blockId = core2.pendingInstruction.loc;
        response.payload[0] = cache2.dataBlocks[blockId][0];
        response.payload[1] = cache2.dataBlocks[blockId][1];
        response.receiver = 0; //no cores receive this data
        response.toMem = 1; //for memory
        response.sender = id;
        response.whichBlock = blockId;//TODO: needs to be updated
    }
}
void execute_instruction(int id) {
    Instruction instr;
    if(id == 1) {
        if(core1.Stalled || program1.PC >= program1.NumInstructions ) {
            ;//keep stalling, stalled by other cores' coherence transactions
        }
        else {//take instruction to execute
            instr = program1.instructions[program1.PC];
            switch(instr.type) {
                case Read:
                    switch (cache1.blockStates[instr.loc])
                    {
                    case Invalid:
                        
                        core1.pendingInstruction = instr;
                        if(transactionInProgress) {//disallow PC to move to next instruction
                            core1.Stalled = 1;       
                        }
                        else {
                            cache1.blockStates[instr.loc] = ISD;
                            request.type = GetS;
                            request.sender = id;
                            request.whichBlock = instr.loc;
                            isIssuingRequest = id;
                            transactionInProgress = id;
                            core1.Stalled = 1;
                        }
                        break;
                    case Shared:
                        core1.registers[instr.regNum] = cache1.dataBlocks[instr.loc][0];
                        break;
                    case Modified:
                        core1.registers[instr.regNum] = cache1.dataBlocks[instr.loc][0];
                        break;
                    default://TODO: Allow SMD to hit
                        NONPROD_ASSERT(0, "atomic transaction violated");
                        break;
                    }
                    break;
                case Write:
                    
                    switch (cache1.blockStates[instr.loc])
                    {
                    case Invalid:
                        core1.pendingInstruction = instr;
                        if(transactionInProgress) {
                            core1.Stalled = 1;
                            
                        }
                        else {
                            cache1.blockStates[instr.loc] = IMD;
                            request.type = GetM;
                            request.sender = id;
                            request.whichBlock = instr.loc;
                            isIssuingRequest = id;
                            transactionInProgress = id;
                            core1.Stalled = 1;
                        }
                        break;
                    case Shared:
                        core1.pendingInstruction = instr;
                        if(transactionInProgress) {
                            core1.Stalled = 1;
                            
                        }
                        else {
                            // NONPROD_ASSERT(0, "smoke test core1 shared no Trans in progress branch");
                            
                            cache1.blockStates[instr.loc] = SMD;
                            request.type = GetM;
                            request.sender = id;
                            request.whichBlock = instr.loc;
                            isIssuingRequest = id;
                            transactionInProgress = id;
                            core1.Stalled = 1;
                        }
                        break;
                    case Modified:
                        // NONPROD_ASSERT(0, "smoke test core1 modified no Trans in progress branch");
                        cache1.dataBlocks[instr.loc][0] = instr.val;
                        break;
                    default:
                        break;
                    }
                    break;
                case Evict:
                    core1.pendingInstruction = instr;
                    if(transactionInProgress) {
                        core1.Stalled = 1;
                    }
                    else {//issue PutM request, set transactionInProgress
                        request.type = PutM;
                        request.sender = id;
                        request.whichBlock = instr.loc;
                        isIssuingRequest = id;
                        core1.Stalled = 1;
                        transactionInProgress = id;
                        cache1.blockStates[instr.loc] = Invalid;
                    }
                    break;
                default:
                    NONPROD_ASSERT(instr.type, "undef instruction type");
                    break;
            }
        }
    }

    if(id == 2) {
        if(core2.Stalled || program2.PC >= program2.NumInstructions) {
            ;//keep stalling, stalled by other cores' coherence transactions
        }
        else {//take instruction to execute
            instr = program2.instructions[program2.PC];
            switch(instr.type) {
                case Read:
                    switch (cache2.blockStates[instr.loc])
                    {
                    case Invalid:
                        PRINT("********* cycle %d, core 2 ", cycle);
                        
                        core2.pendingInstruction = instr;
                        if(transactionInProgress) {//disallow PC to move to next instruction
                            core2.Stalled = 1;
                        }
                        else {
                            cache2.blockStates[instr.loc] = ISD;
                            request.type = GetS;
                            request.sender = id;
                            request.whichBlock = instr.loc;
                            isIssuingRequest = id;
                            transactionInProgress = id;
                            core2.Stalled = 1;
                            PRINT("cache 2 requesting %d read access \n", instr.loc);
                        }
                        break;
                    case Shared:
                        core2.registers[instr.regNum] = cache2.dataBlocks[instr.loc][0];
                        break;
                    case Modified:
                        core2.registers[instr.regNum] = cache2.dataBlocks[instr.loc][0];
                        break;
                    default://TODO: Allow SMD to hit
                        NONPROD_ASSERT(0, "atomic transaction violated");
                        break;
                    }
                    break;
                case Write:
                    // NONPROD_ASSERT(0, "smoke test for write of core 2");
                    switch (cache2.blockStates[instr.loc])
                    {
                    case Invalid:
                        core2.pendingInstruction = instr;
                        if(transactionInProgress) {
                            core2.Stalled = 1;
                        }
                        else {
                            cache2.blockStates[instr.loc] = IMD;
                            request.type = GetM;
                            request.sender = id;
                            request.whichBlock = instr.loc;
                            isIssuingRequest = id;
                            transactionInProgress = id;
                            core2.Stalled = 1;
                        }
                        break;
                    case Shared:
                        core2.pendingInstruction = instr;
                        if(transactionInProgress) {
                            core2.Stalled = 1;
                        }
                        else {
                            cache2.blockStates[instr.loc] = SMD;
                            request.type = GetM;
                            request.sender = id;
                            request.whichBlock = instr.loc;
                            isIssuingRequest = id;
                            transactionInProgress = id;
                            core2.Stalled = 1;
                        }
                        break;
                    case Modified:
                        cache2.dataBlocks[instr.loc][0] = instr.val;
                        break;
                    default:
                        break;
                    }
                    break;
                case Evict:
                    core2.pendingInstruction = instr;
                    if(transactionInProgress) {
                        core2.Stalled = 1;
                    }
                    else {//issue PutM request, set transactionInProgress
                        request.type = PutM;
                        request.sender = id;
                        request.whichBlock = instr.loc;
                        isIssuingRequest = id;
                        core2.Stalled = 1;
                        transactionInProgress = id;
                        cache2.blockStates[instr.loc] = Invalid;
                    }
                    break;
                default:
                    NONPROD_ASSERT(0, "unrecognised instruction type");
                    break;
            }
        }
    }

}
void core_reacts(int id) {
    
    core_deal_with_previous_bus_msg(id);
    // if(early_terminate(id))
    //     return;
    if(transactionInProgress == id) {
        //myOwn transaction
        if(snooping_bus.type == PutM) { //TOCHECK: last cycle was evict
            compose_PutMData(id);
        }
    }
    else {
    
        execute_instruction(id);
    }
    update_PC(id);
}

#ifdef DEBUG_MODE
void cores_react() {
    for(int i = 1; i <= NUM_CORES; i++) {
        core_reacts(i);
    }
}
#elif defined(NONDET_CHECK) //|| defined(PRODUCTION)  //exhaustive check
void cores_react() {
    int done[NUM_CORES + 1] = {0, 0, 0};
    for(int i = 0; i < NUM_CORES; i++) {
        unsigned id = nondet();
        
        NONPROD_ASSUME(1 <= id && id <= NUM_CORES);
        NONPROD_ASSUME(!done[id]);
        // NONPROD_ASSERT(0, "SMOKE NONDET_CHECK");
       
        //printf("chosen core %d to execute\n", id + 1);
        core_reacts(id);
        done[id] = 1;
    }
}
#elif NONDET_CHECK2 //A faster exhaustive check?
void cores_react() {
    int done[NUM_CORES + 1] = {0, 0, 0};
    for(int i = 0; i < NUM_CORES; i++) {
        unsigned id = ((unsigned) nondet() ) % 2 + 1;

        NONPROD_ASSUME(1 <= id && id <= NUM_CORES);
        NONPROD_ASSUME(!done[id]);
        core_reacts(id);
        done[id] = 1;
    }
}
#else //(normal cbmc mode) else choose one order so we check quickly
void cores_react() {
    for(int i = 1; i <= NUM_CORES; i++) {
        core_reacts(i);
    }
}
#endif

void initialise_cores() {
    core1.Stalled = 0;
    core2.Stalled = 0;
}

void save_current_msg_for_next_cycle() {
    PRINT0("saving message on bus\n");
    if(snooping_bus.type != Idle) {
        PRINT0("bus was not idle\n");
        PRINT("bus tepe is %d\n", snooping_bus.type);
        if(snooping_bus.type == Data) {
            PRINT("On cycle %d snooped Data from bus", cycle);
        }
        hasPreviousBusMsg = 1;
        previousBusMsg = snooping_bus;
        //NONPROD_ASSERT(previousBusMsg.type != GetM, "Data never on bus?");
    }
    else {
        hasPreviousBusMsg = 0;
        //clear bus message? Or leave it as it is?
    }
    snooping_bus.type = Idle;
}

void update_bus_msg_for_next_cycle(){
    // NONPROD_ASSERT(!(isIssuingRequest && isIssuingResponse), "cannot be issuing two to bus");
    if(isIssuingRequest){
        snooping_bus = request;
        isIssuingRequest = 0;
    }
    else if(isIssuingResponse){
        snooping_bus = response;
        isIssuingResponse = 0;
    }
    else {
        snooping_bus.type = Idle;
    }

}

void mem_react() {
    int blockId;
    PRINT("cycle %d \n", cycle);
    PRINT2("memory react to message type %d, haspreviousbusmsg is %d\n", previousBusMsg.type, hasPreviousBusMsg);
    if(hasPreviousBusMsg) {
        PRINT("mem is reacting to %d\n", previousBusMsg.type);
        blockId = previousBusMsg.whichBlock;
        switch(previousBusMsg.type) 
        {
        case GetS:
            switch(llc.blockStates[blockId]) 
            {
            case IorS:
                response.payload[0] = llc.dataBlocks[blockId][0];
                response.payload[1] = llc.dataBlocks[blockId][1];
                response.receiver = previousBusMsg.sender;
                response.sender = 0;
                response.toMem = 0;
                response.type = Data;
                response.whichBlock = blockId;
                isIssuingResponse = 1;
                break;
            case MMem:
                PRINT("M->IorSD on cycle %d \n", cycle);
                llc.blockStates[blockId] = IorSD;
                break;
            default: //TOTEST: should not receive GetS in IorSD
                NONPROD_ASSERT(llc.blockStates[blockId] != IorSD, "shouldn't receive GetS request while in IorSD state: expecting data");
                break;
            }
            break;
        case GetM:
            PRINT("GetM to process with block state: %d\n", llc.blockStates[blockId]);
            switch(llc.blockStates[blockId]) 
            {
            case IorS:
                // NONPROD_ASSERT(transactionInProgress, "transaction should be in progress while llc responding with data");
                response.payload[0] = llc.dataBlocks[blockId][0];
                response.payload[1] = llc.dataBlocks[blockId][1];
                response.receiver = previousBusMsg.sender;
                response.sender = 0;
                response.toMem = 0;
                response.type = Data;
                response.whichBlock = blockId;
                isIssuingResponse = 1;
                llc.blockStates[blockId] = MMem;
                break;
            case MMem:
                //PRINT("FOR a GetM request from %d for an M block, should reach here\n", previousBusMsg.sender);
                break;
            default:
                break;  
            }
            break;
        case PutM:
            llc.blockStates[blockId] = IorSD;
            break;
        case Data://TOTEST: llc.blockStates[blockId] was IorSD
            if(previousBusMsg.toMem)
            {    
                PRINT0("this is data to mem\n");
                llc.blockStates[blockId] = IorS;
                llc.dataBlocks[blockId][0] = previousBusMsg.payload[0];
                llc.dataBlocks[blockId][1] = previousBusMsg.payload[1];
                //transactionInProgress = 0;
                core1.Stalled = 0;
                core2.Stalled = 0;
            }
            break;
        default://TOTEST: should not be idle since hasPrevious... is nonzero
            break;
        }
    }
    // hasPreviousBusMsg = 0;
}

int main() {
    

    // NONPROD_ASSERT(0, "smoke");

    //TSO litmus test
    TSO();
    

    
    initialise_bus();

    initialise_mem();

    initialise_cache();

    initialise_cores();

    
    while(cycle < 30) {
        cores_react();
        mem_react();
        save_current_msg_for_next_cycle();
        PRINT("HA%D\n", cycle);
        PRINT2("hasPreviousBusmsg: %d, previousBusMsg type: %d\n", hasPreviousBusMsg, previousBusMsg.type);
        PRINT2("Who sent message: %d, for which block: %d (0-X, 1-Y), ", previousBusMsg.sender, previousBusMsg.whichBlock);
        PRINT("For whom: %d \n", previousBusMsg.receiver);
        update_bus_msg_for_next_cycle();
        if(program1.PC >= program1.NumInstructions && program2.PC >= program2.NumInstructions && !core1.Stalled && !core2.Stalled && !transactionInProgress)
            break;
        
        cycle++;
    }

    // IMPORTANT_ASSERT(program1.NumInstructions + 1 >= program1.PC >= program1.NumInstructions && program2.NumInstructions + 1 >= program2.PC >= program2.NumInstructions, "finished all instructions");
    // IMPORTANT_ASSERT(program1.NumInstructions + 1 >= program1.PC >= program1.NumInstructions && program2.NumInstructions + 1 >= program2.PC >= program2.NumInstructions, "finished all instructions");

    NONPROD_ASSERT(cycle < 30, "didn't hit cycle maximum 30");
    IMPORTANT_ASSERT(program1.NumInstructions + 1 >= program1.PC, "program 1 PC not too far beyond last instruction");
    IMPORTANT_ASSERT(program2.NumInstructions + 1 >= program2.PC, "program 2 pC not too far beyond last instruction" );
    IMPORTANT_ASSERT(!(core1.registers[1] == 0 && core2.registers[0] == 0), "Cannot happen: r1 read 0, and r0 read 0");
    IMPORTANT_ASSERT(!transactionInProgress, "transactionInProgress was kept positive when it should not be");
    IMPORTANT_ASSERT(!core1.Stalled, "core 1 have been stalled when it should not be");
    IMPORTANT_ASSERT(!core2.Stalled, "core 2 have been stalled when it should not be");
    PRINT2("%d %d\n", program1.PC, program2.PC);
    
    IMPORTANT_ASSERT(!(core1.registers[1] == 0 && core2.registers[0] == 1), "Should fail on a non-deterministic run: legal outcome r1 (core 1's r1 loaded Y's value) = 0, r0 = 1");
    IMPORTANT_ASSERT(!(core1.registers[1] == 1 && core2.registers[0] == 0), "Should fail on a nondet check: legal out come r1 = 1, r0 = 0");
    IMPORTANT_ASSERT(!(core1.registers[1] == 1 && core2.registers[0] == 1), "Should fail on a non-det check: legal outcome r1 = 1, r0 = 1");
    // IMPORTANT_ASSERT(program1.PC >= program1.NumInstructions, "PC1 beyond last intruction?");
    // IMPORTANT_ASSERT(program2.PC >= program2.NumInstructions, "PC2 beyond last instruction?");
    // IMPORTANT_ASSERT(cache1.dataBlocks[0][0] == 1, "cache 1 correctly updated");
    // IMPORTANT_ASSERT(0, "smoke test");
    

    //random reads and write
    //consistency properties being maintained
    //eg. same location, both think they havec E access: shouldn't happen
    //
    return 0;
}







