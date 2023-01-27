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
Program program[2];
Cache cache[2];
Core core[2];
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
    program[0].PC = 0;
    program[0].NumInstructions = 2;
    program[0].instructions[0].type = Write;
    program[0].instructions[0].val = 1;
    program[0].instructions[0].loc = 0;//write x
    program[0].instructions[1].type = Read;
    program[0].instructions[1].val = 1;
    program[0].instructions[1].loc = 1;//read y
    program[0].instructions[1].regNum = 1; //core 1 reads to r1

    program[1].PC = 0;
    program[1].NumInstructions = 2;
    program[1].instructions[0].type = Write;
    program[1].instructions[0].val = 1; 
    program[1].instructions[0].loc = 1;//write y
    program[1].instructions[1].type = Read;
    program[1].instructions[1].val = 1;
    program[1].instructions[1].loc = 0;//read x
    program[1].instructions[1].regNum = 0; //core 2 reads to r0
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
    cache[0].blockStates[0] = Invalid;
    cache[0].blockStates[1] = Invalid;
    cache[0].dataBlocks[0][0] = 99;
    cache[0].dataBlocks[1][0] = 88;
    //the next 2 lines do not matter 
    cache[0].dataBlocks[0][1] = 0;
    cache[0].dataBlocks[1][1] = 0;
    hasPreviousBusMsg = 0;
    cache[0].doneOneThing = 0;
    

    //cache 2
    cache[1].blockStates[0] = Invalid;
    cache[1].blockStates[1] = Invalid;
    cache[1].dataBlocks[0][0] = 77;
    cache[1].dataBlocks[1][0] = 66;
    //the next 2 lines do not matter 
    cache[1].dataBlocks[0][1] = 0;
    cache[1].dataBlocks[1][1] = 0;
    hasPreviousBusMsg = 0;
    cache[1].doneOneThing = 0;


}



void cache_deal_OwnGetS(int id) {
    return; //own message, nothing to do
}

void cache_deal_OtherGetS(int id) {
    int thisBlock;
    int requestor;
    thisBlock = previousBusMsg.whichBlock;
    switch (cache[id - 1].blockStates[thisBlock])
    {
    case Invalid:
        //ignore
        break;
    case Shared:
        break; //ignore
    case Modified:
        //downgrade to shared state, send data to requestor and mem
        cache[id - 1].blockStates[thisBlock] = Shared;
        requestor = previousBusMsg.sender;
        response.type = Data;
        response.payload[0] = cache[id - 1].dataBlocks[thisBlock][0];
        response.payload[1] = cache[id - 1].dataBlocks[thisBlock][1];
        response.receiver = requestor;
        response.toMem = 1; //also write back to cache
        response.sender = id;
        response.whichBlock = thisBlock;
        isIssuingResponse = 1;
        cache[id - 1].doneOneThing = 1;
        break;
    default:
        NONPROD_ASSERT(0, "AT, should never be in transient states when another processor is issuing coherence request");
        break;
    }
}

void cache_deal_OtherGetM(int id) {
    int thisBlock;
    int requestor;
    thisBlock = previousBusMsg.whichBlock;
    switch (cache[id - 1].blockStates[thisBlock])
    {
    case Invalid:
        //ignore
        break;
    case Shared:
        cache[id - 1].blockStates[thisBlock] = Invalid;
        break; 
    case Modified:
        //downgrade to shared state, send data to requestor and mem
        cache[id - 1].blockStates[thisBlock] = Invalid;
        requestor = previousBusMsg.sender;
        response.type = Data;
        response.payload[0] = cache[id - 1].dataBlocks[thisBlock][0];
        response.payload[1] = cache[id - 1].dataBlocks[thisBlock][1];
        response.receiver = requestor;
        response.toMem = 0; //ownership goes to another cache
        response.sender = id;
        response.whichBlock = thisBlock;
        cache[id - 1].doneOneThing = 1;
        isIssuingResponse = 1;
        break;
    default:
        NONPROD_ASSERT(0, "AT, should never be in transient states");
        break;
    }
}

void cache_deal_OwnGetM(int id) {
    return; //ignore since my own transaction
}
void cache_deal_OwnPutM(int id) {
    return;
}
void core_deal_with_previous_bus_msg(int id) {
    int thisBlock;
    Instruction pending;

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
            if(previousBusMsg.receiver != id)
                break;
            PRINT("smoke after break %d \n", thisBlock);
            cache[id - 1].dataBlocks[thisBlock][0] = previousBusMsg.payload[0];
            cache[id - 1].dataBlocks[thisBlock][1] = previousBusMsg.payload[1];
            cache[id - 1].doneOneThing = 1;
            transactionInProgress = 0;
            core[0].Stalled = 0;
            core[1].Stalled = 0;
            pending = core[id - 1].pendingInstruction;
            
            switch(cache[id - 1].blockStates[thisBlock]) {
                case ISD:
                    cache[id - 1].blockStates[thisBlock] = Shared;
                    //& complete previous instruction load
                    core[id - 1].registers[pending.regNum] = cache[id - 1].dataBlocks[thisBlock][0];
                    NONPROD_ASSERT(thisBlock == pending.loc, "Data block id should be the same as the read instruction's read location");
                    break;
                case IMD:
                    cache[id - 1].blockStates[thisBlock] = Modified;
                    //& complete previous instruction store
                    cache[id - 1].dataBlocks[thisBlock][0] = pending.val;
                    PRINT2("block %d has value %d now\n", thisBlock, pending.val);
                    break;
                case SMD:
                    cache[id - 1].blockStates[thisBlock] = Modified;
                    //& complete previous instruction store
                    cache[id - 1].dataBlocks[thisBlock][0] = pending.val;
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
}

void update_PC(int id) {
    if (!core[id - 1].Stalled && program[id - 1].PC <= program[id - 1].NumInstructions) {
        program[id - 1].PC++;
    }
}

int early_terminate(int id) {
    return cache[id - 1].doneOneThing;
}
void compose_PutMData(int id) {
    isIssuingResponse = 1;
    response.type = Data;
    int blockId;
    blockId = core[id - 1].pendingInstruction.loc;
    response.payload[0] = cache[id - 1].dataBlocks[blockId][0];
    response.payload[1] = cache[id - 1].dataBlocks[blockId][1];
    response.receiver = 0; //no cores receive this data
    response.toMem = 1; //for memory
    response.sender = id;
    response.whichBlock = blockId;//TODO: needs to be updated
}
void execute_instruction(int id) {
    Instruction instr;
    if(core[id - 1].Stalled || program[id - 1].PC >= program[id - 1].NumInstructions ) {
        ;//keep stalling, stalled by other cores' coherence transactions
    }
    else {//take instruction to execute
        instr = program[id - 1].instructions[program[id - 1].PC];
        switch(instr.type) {
            case Read:
                switch (cache[id - 1].blockStates[instr.loc])
                {
                case Invalid:
                    
                    core[id - 1].pendingInstruction = instr;
                    if(transactionInProgress) {//disallow PC to move to next instruction
                        core[id - 1].Stalled = 1;       
                    }
                    else {
                        cache[id - 1].blockStates[instr.loc] = ISD;
                        request.type = GetS;
                        request.sender = id;
                        request.whichBlock = instr.loc;
                        isIssuingRequest = id;
                        transactionInProgress = id;
                        core[id - 1].Stalled = 1;
                    }
                    break;
                case Shared:
                    core[id - 1].registers[instr.regNum] = cache[id - 1].dataBlocks[instr.loc][0];
                    break;
                case Modified:
                    core[id - 1].registers[instr.regNum] = cache[id - 1].dataBlocks[instr.loc][0];
                    break;
                default://TODO: Allow SMD to hit
                    NONPROD_ASSERT(0, "atomic transaction violated");
                    break;
                }
                break;
            case Write:
                switch (cache[id - 1].blockStates[instr.loc])
                {
                case Invalid:
                    core[id - 1].pendingInstruction = instr;
                    if(transactionInProgress) {
                        core[id - 1].Stalled = 1;
                    }
                    else {
                        cache[id - 1].blockStates[instr.loc] = IMD;
                        request.type = GetM;
                        request.sender = id;
                        request.whichBlock = instr.loc;
                        isIssuingRequest = id;
                        transactionInProgress = id;
                        core[id - 1].Stalled = 1;
                    }
                    break;
                case Shared:
                    core[id - 1].pendingInstruction = instr;
                    if(transactionInProgress) {
                        core[id - 1].Stalled = 1;
                    }
                    else {
                        cache[id - 1].blockStates[instr.loc] = SMD;
                        request.type = GetM;
                        request.sender = id;
                        request.whichBlock = instr.loc;
                        isIssuingRequest = id;
                        transactionInProgress = id;
                        core[id - 1].Stalled = 1;
                    }
                    break;
                case Modified:
                    cache[id - 1].dataBlocks[instr.loc][0] = instr.val;
                    break;
                default:
                    break;
                }
                break;
            case Evict:
                core[id - 1].pendingInstruction = instr;
                if(transactionInProgress) {
                    core[id - 1].Stalled = 1;
                }
                else {//issue PutM request, set transactionInProgress
                    request.type = PutM;
                    request.sender = id;
                    request.whichBlock = instr.loc;
                    isIssuingRequest = id;
                    core[id - 1].Stalled = 1;
                    transactionInProgress = id;
                    cache[id - 1].blockStates[instr.loc] = Invalid;
                }
                break;
            default:
                NONPROD_ASSERT(instr.type, "undef instruction type");
                break;
        }
    }
}

void core_reacts(int id) {
    core_deal_with_previous_bus_msg(id);
    if(transactionInProgress == id) {
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
    core[0].Stalled = 0;
    core[1].Stalled = 0;
}

void save_current_msg_for_next_cycle() {
    if(snooping_bus.type != Idle) {
        hasPreviousBusMsg = 1;
        previousBusMsg = snooping_bus;
    }
    else {
        hasPreviousBusMsg = 0;
    }
    snooping_bus.type = Idle;
}

void update_bus_msg_for_next_cycle(){
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
    if(hasPreviousBusMsg) {
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
                llc.blockStates[blockId] = IorSD;
                break;
            default: //TOTEST: should not receive GetS in IorSD
                break;
            }
            break;
        case GetM:
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
                llc.blockStates[blockId] = IorS;
                llc.dataBlocks[blockId][0] = previousBusMsg.payload[0];
                llc.dataBlocks[blockId][1] = previousBusMsg.payload[1];
                //transactionInProgress = 0;
                core[0].Stalled = 0;
                core[1].Stalled = 0;
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
        if(program[0].PC >= program[0].NumInstructions && program[1].PC >= program[1].NumInstructions && !core[0].Stalled && !core[1].Stalled && !transactionInProgress)
            break;
        
        cycle++;
    }


    IMPORTANT_ASSERT(!(core[0].registers[1] == 0 && core[1].registers[0] == 0), "Cannot happen: r1 read 0, and r0 read 0");
    IMPORTANT_ASSERT(!(core[0].registers[1] == 0 && core[1].registers[0] == 1), "Should fail on a non-deterministic run: legal outcome r1 (core 1's r1 loaded Y's value) = 0, r0 = 1");
    IMPORTANT_ASSERT(!(core[0].registers[1] == 1 && core[1].registers[0] == 0), "Should fail on a nondet check: legal out come r1 = 1, r0 = 0");
    IMPORTANT_ASSERT(!(core[0].registers[1] == 1 && core[1].registers[0] == 1), "Should fail on a non-det check: legal outcome r1 = 1, r0 = 1");
  

    //random reads and write
    //consistency properties being maintained
    //eg. same location, both think they havec E access: shouldn't happen
    //
    return 0;
}







