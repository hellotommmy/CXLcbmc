#include "fake_cluster.h"
// typedef struct {
#define BYTES_PER_BLOCK_HA 2
#define MAX_BLOCKS_HA 2
#define NUM_CLUSTERS 2
#define MAX_MESSAGES_CHANNEL 8
// } DeviceAgent;

typedef enum {
    RdShared,
    RdOwn,
    RdCurr,
    RdAny,
    RdOwnNoData,
    CLFlush,
    CacheFlushed,
    CleanEvict,
    DirtyEvict,
    CleanEvictNoData,

    ItoMWr,
    WrCurr, //is called MemWr, but clash with cxl.mem
    WOWrInv,
    WrInv,

} D2HRequestType;

typedef struct {
    D2HRequestType type;
    int whichBlock;

    //information needed by a tracker
    int CQID;
    int requestorCore;
    int requestorCluster;
    int DataArrivedBeforeGO;
} D2HRequest;

typedef enum {
    SnpData,
    SnpInv,
    SnpCurr,
} H2DRequestType;

typedef struct {
    H2DRequestType type;
    int whichBlock;
    int UQID;

    //information needed by a tracker
    //int CQID;
    int requestorCore;
    int requestorCluster;
    int DataArrivedBeforeGO;
} H2DRequest;

typedef struct {
    H2DRequestType snoopType;
    HABlockTypes cachelineTypeBeforeSnoop;
    int UQID;
    int requestorCluster;
    int requestorCore;


} CXLTempTracker;

typedef enum {
    RspIHitI,
    RspIHitSE,
    RspSHitSE,
    RspVHitV,
    RspSFwdM,
    RspIFwdM,
    RspVFwdV,
} D2HResponseType;

typedef struct {
    D2HResponseType type;
    int whichBlock;

    //information needed by a tracker
    int CQID;
    int requestorCore;
    int requestorCluster;
    int DataArrivedBeforeGO;
} D2HResponse;

typedef enum {
    GO,
    WritePull,
    FastGO_WritePull,
} H2DResponseType;

typedef struct {
    H2DResponseType type;
    HABlockTypes MESI_State;
    int UQID;

    //information needed by a tracker
    //int CQID;
    int requestorCore;
    int requestorCluster;
    int DataArrivedBeforeGO;
    int whichBlock;
} H2DResponse;

typedef struct {
    int UQID; //header, we only model the UQID field for now
    int payload[BYTES_PER_BLOCK_HA];

    //information needed by a tracker
    int requestorCore;
    int requestorCluster;

    int whichBlock;
} D2HData;

typedef struct {
    int CQID; //header, only model CQID for the moment
    int payload[BYTES_PER_BLOCK_HA];

    //information needed by a tracker
    int requestorCore;
    int requestorCluster;
    int DataArrivedBeforeGO;
    int whichBlock;
} H2DData;





typedef struct {
    int dataBlocks[MAX_BLOCKS_HA][BYTES_PER_BLOCK_HA];
    int stateBitVector[MAX_BLOCKS_HA][NUM_CLUSTERS + 1];   //bit vector
    int existsValidCopy[MAX_BLOCKS_HA]; 
} HA;




int CQID_counter = 0;
int globalCounter = 0;
D2HRequest D2HReq1[MAX_MESSAGES_CHANNEL], D2HReq2[MAX_MESSAGES_CHANNEL];
D2HRequest D2HReqToIssue1, D2HReqToIssue2, D2HReqToProcess1, D2HReqToProcess2;
int isIssuingD2HReq1, isIssuingD2HReq2, prevD2HReqBusy1, prevD2HReqBusy2;
int prevD2HBlocked1, prevD2HBlocked2;

H2DRequest H2DReq1[MAX_MESSAGES_CHANNEL], H2DReq2[MAX_MESSAGES_CHANNEL];
H2DRequest H2DReqToIssue1, H2DReqToIssue2, H2DReqToProcess1, H2DReqToProcess2;
int isIssuingH2DReq1, isIssuingH2DReq2, prevH2DReqBusy1, prevH2DReqBusy2;
int prevH2DReqBlocked1, prevH2DReqBlocked2; 

H2DResponse H2DResp1[MAX_MESSAGES_CHANNEL], H2DResp2[MAX_MESSAGES_CHANNEL], H2DRespToIssue1, H2DRespToIssue2, H2DRespToProcess1, H2DRespToProcess2;
H2DResponse H2DRespToIssue1, H2DRespToIssue2, H2DRespToProcess1, H2DRespToProcess2;
int isIssuingH2DResp1, isIssuingH2DResp2, prevH2DRespBusy1, prevH2DRespBusy2;

D2HResponse D2HResp1[MAX_MESSAGES_CHANNEL], D2HResp2[MAX_MESSAGES_CHANNEL], D2HRespToIssue1, D2HRespToIssue2, D2HRespToProcess1, D2HRespToProcess2;
D2HResponse D2HRespToIssue1, D2HRespToIssue2, D2HRespToProcess1, D2HRespToProcess2;
int isIssuingD2HResp1, isIssuingD2HResp2, prevD2HRespBusy1, prevD2HRespBusy2;

D2HData D2HData1[MAX_MESSAGES_CHANNEL], D2HData2[MAX_MESSAGES_CHANNEL], D2HDataToIssue1, D2HDataToIssue2, D2HDataToProcess1, D2HDataToProcess2;
D2HData D2HDataToIssue1, D2HDataToIssue2, D2HDataToProcess1, D2HDataToProcess2;
int isIssuingD2HData1, isIssuingD2HData2, prevD2HDataBusy1, prevD2HDataBusy2;

H2DData H2DData1[MAX_MESSAGES_CHANNEL], H2DData2[MAX_MESSAGES_CHANNEL], H2DDataToIssue1, H2DDataToIssue2, H2DDataToProcess1, H2DDataToProcess2;
H2DData H2DDataToIssue1, H2DDataToIssue2, H2DDataToProcess1, H2DDataToProcess2;
int isIssuingH2DData1, isIssuingH2DData2, prevH2DDataBusy1, prevH2DDataBusy2;
int prevH2DDataBlocked1, prevH2DDataBlocked2;

HA Host;

CXLTempTracker TempTracker1, TempTracker2;


//DCOH store for each HA block, what state this block is in this cluster
//for example, X --> invalid,  y --> Exclusive
//individual cores states are not recorded
HABlockTypes DCOH1[MAX_BLOCKS_HA], DCOH2[MAX_BLOCKS_HA];

void init_DCOH() {
    DCOH1[0] = MESI_I;
    DCOH1[1] = MESI_I;
    DCOH2[0] = MESI_I;
    DCOH2[1] = MESI_I;
}
void init_tracker_HA(D2HRequest * req, HABlockTypes typeToGive) {
    HomeTrackers[trackersCountHome].CQID = req->CQID;
    HomeTrackers[trackersCountHome].blockNum = req->whichBlock;
    HomeTrackers[trackersCountHome].DataArrivedBeforeGO = 0;
    HomeTrackers[trackersCountHome].requestorCluster = req->requestorCluster;
    HomeTrackers[trackersCountHome].requestorCore = req->requestorCore;
    HomeTrackers[trackersCountHome].typeToGive = typeToGive;
    trackersCountHome++;
}
int D2HReq1Counter, D2HReq2Counter, H2DReq1Counter, H2DReq2Counter, H2DResp1Counter, H2DResp2Counter, D2HResp1Counter, D2HResp2Counter;
int D2HData1Counter, D2HData2Counter, H2DData1Counter, H2DData2Counter;

void generate_H2DReq(D2HRequest * d2h, H2DRequest * h2d) {
    h2d->whichBlock = d2h->whichBlock;
    h2d->UQID = d2h->CQID;
    h2d->requestorCluster = d2h->requestorCluster;
    h2d->requestorCore = d2h->requestorCore;
    h2d->DataArrivedBeforeGO = 0;
    //h2d->type is not set, determined by the clause: is it RdOwn? RdAny? RdShared?
}
void generate_H2DResp(D2HRequest * d2h, H2DResponse * h2d) { //used when no sharers exists, HA immediately replies
    h2d->whichBlock = d2h->whichBlock;
    h2d->UQID = d2h->CQID;
    h2d->requestorCluster = d2h->requestorCluster;
    h2d->requestorCore = d2h->requestorCore;
    h2d->DataArrivedBeforeGO = 0;
}
void get_most_recent_data(int requestorClusterId, int blockId) {
    //get the most up-to-date data from owner, downgrading the owner state into S
    //In the 2-cluster case, get_most_recent_data is called only in the below occasion: 
    //if 1 requests, 2 is owner (E or M), or the other way around
    if(requestorClusterId == 1) {
        NONPROD_ASSERT(Host.stateBitVector[blockId][0] == 2, "2 should be the owner when get_most_recent_data is called on behalf of another cluster");
        isIssuingH2DReq2 = 1;
        H2DReqToIssue2.type = SnpData;
        generate_H2DReq(&D2HReqToProcess1, &H2DReqToIssue2);
    }
    else {
        NONPROD_ASSERT(Host.stateBitVector[blockId][0] == 1, "1 should be the owner when get_most_recent_data is called on behalf of another cluster");
        isIssuingH2DReq1 = 1;
        H2DReqToIssue1.type = SnpData;
        generate_H2DReq(&D2HReqToProcess2, &H2DReqToIssue1);    
    }
}
void invalidate_sharers(int requestorClusterId, int blockId) {
    // for(int i = 1; i <= NUM_CLUSTERS; i++) {//code for when there are more than 2 clusters
    //         //if exists sharers, for all sharers, send invalidation via H2D request channel
    //         if(Host.stateBitVector[blockId][i]){
    //             isIssuingH2DReq2 = 1;
    //             H2DReqToIssue2.type = SnpInv;
    //             generate_H2DReq(&D2HReqToProcess1, &H2DReqToIssue2);
    //         }
    // }
    //1 requesting causes 2 to be invalidated, vice versa
    if(requestorClusterId == 1){
        NONPROD_ASSERT(Host.stateBitVector[blockId][2], "the other cluster (2) should be a sharer for invalidate_sharers to be called");
        isIssuingH2DReq2 = 1;
        H2DReqToIssue2.type = SnpInv;
        generate_H2DReq(&D2HReqToProcess1, &H2DReqToIssue2);
    }
    else {
        NONPROD_ASSERT(Host.stateBitVector[blockId][1], "the other cluster (1) should be a sharer for invalidate_sharers to be called");
        isIssuingH2DReq1 = 1;
        H2DReqToIssue1.type = SnpInv;
        generate_H2DReq(&D2HReqToProcess2, &H2DReqToIssue1);
    }
}

void generate_H2DResp_from_tracker(Tracker * t, H2DResponse * h2d) {
    h2d->DataArrivedBeforeGO = t->DataArrivedBeforeGO;
    h2d->MESI_State = t->typeToGive;
    h2d->requestorCluster = t->requestorCluster;
    h2d->requestorCore = t->requestorCore;
    h2d->type = GO;
    h2d->UQID = t->CQID;
    h2d->whichBlock = t->blockNum;
}

void deallocate_tracker(int trackerId) {
    for(int j = trackerId; j < trackersCountHome - 1; j++) {
        HomeTrackers[j] = HomeTrackers[j + 1];
    }
    trackersCountHome--;
}

void generate_H2DData_from_HA(H2DData * h2d, int blockId, H2DResponse * resp) {
    h2d->payload[0] = Host.dataBlocks[blockId][0];
    h2d->payload[1] = Host.dataBlocks[blockId][1];
    h2d->CQID = resp->UQID;
    h2d->DataArrivedBeforeGO = resp->DataArrivedBeforeGO;
    h2d->requestorCluster = resp->requestorCluster;
    h2d->requestorCore = resp->requestorCore;
}

void HA_acts() {
    //choose 1 D2H request to reply (if any), choose 1 D2H response to process (if any), 1 D2H data to forward (if any)
    printf("prevD2HReqBusy1: %d, prevD2HBlocked1: %d\n", prevD2HReqBusy1, prevD2HBlocked1);
    if(prevD2HReqBusy1){
        printf("HA dealing with D2H req\n");
        //remember the block, if block under coherence transaction, postpone dealing with current D2HReq
        int blockId = D2HReqToProcess1.whichBlock;
        for(int i = 0; i < trackersCountHome; i++) {
            if(HomeTrackers[i].blockNum == blockId) {
                //delay processing if exists an ongoing transaction for same blockId
                prevD2HBlocked1 = 1;
                break;
                //Different strategies to determine next message processed by HA:
                //(a) put to process message back to D2H channel? 
                //(b) keep stalling on this message until transaction for the same block completes
                //either way, prevD2HBlocked1 signals that a message waiting to be processed is blocked
            }
        }
        if(!prevD2HBlocked1){//if the current request is not blocked
            switch(D2HReqToProcess1.type) {
                case RdOwn:
                    printf("dealing rdown\n");
                    NONPROD_ASSERT(Host.stateBitVector[blockId][0] != 1 , "Buried cache state rule: the requestor should not be owner--if it is it should not need to send an ownership request");
                    if(Host.existsValidCopy[blockId]) {//if there exists at least one valid copy in peer caches
                        invalidate_sharers(1, blockId);//the bitvector will be updated after SnpInv got a response from the device
                        init_tracker_HA(&D2HReqToProcess1, MESI_E);
                        if(!Host.stateBitVector[blockId][0]) {
                            //TODO: if not owned, can send data from HA now??
                            //TODO: check the meaning of Data "ordering with other transactions"
                            printf("sending data to requestor from HA\n");
                            H2DDataToIssue1.payload[0] = Host.dataBlocks[blockId][0];
                            H2DDataToIssue1.payload[1] = Host.dataBlocks[blockId][1];
                            isIssuingH2DData1 = 1;
                            H2DDataToIssue1.whichBlock = blockId;
                            H2DDataToIssue1.requestorCluster = D2HReqToProcess1.requestorCluster;
                            H2DDataToIssue1.requestorCore = D2HReqToProcess1.requestorCore;
                            H2DDataToIssue1.CQID = D2HReqToProcess1.CQID;

                        }
                        else {
                            //someone other than 1 owns data!
                            printf("invalidate owner!\n");
                            isIssuingH2DReq2 = 1;
                            //currently "other" can only be 2
                            NONPROD_ASSERT(Host.stateBitVector[blockId][2], "only 1 owner in MESI protocol, should be 2 since 1 is requesting");
                            generate_H2DReq(&D2HReqToProcess1, &H2DReqToIssue2);
                            H2DReqToIssue2.type = SnpInv;
                            

                        }
                    }
                    else {
                        printf("no one owns it yet and no sharer\n");
                        NONPROD_ASSERT(Host.stateBitVector[blockId][2] == 0, "no sharers anywhere, cluster 2 should not have a valid copy");
                        //the block is not shared by any caches, no tracker needs to be set up, response is sent immediately
                        generate_H2DResp(&D2HReqToProcess1, &H2DRespToIssue1);
                        H2DRespToIssue1.MESI_State = MESI_E;
                        H2DRespToIssue1.type = GO;
                        isIssuingH2DResp1 = 1;//
                        printf("Now issuing H2D response called GO\n");
                        //set onwer state in bitvector
                        Host.stateBitVector[blockId][0] = 1; //cluster 1 is going to own block
                        Host.stateBitVector[blockId][1] = 1;
                        Host.existsValidCopy[blockId] = 1; //now requestor has a valid copy
                        //TODO: also send the data
                        
                        H2DDataToIssue1.payload[0] = Host.dataBlocks[blockId][0];
                        H2DDataToIssue1.payload[1] = Host.dataBlocks[blockId][1];
                        isIssuingH2DData1 = 1;
                        H2DDataToIssue1.whichBlock = blockId;
                        H2DDataToIssue1.requestorCluster = D2HReqToProcess1.requestorCluster;
                        H2DDataToIssue1.requestorCore = D2HReqToProcess1.requestorCore;
                        H2DDataToIssue1.CQID = D2HReqToProcess1.CQID;
                    }
                    break;
                case RdShared:
                    if(Host.stateBitVector[blockId][0]) {
                        //if someone owns the block, need to get data from it
                        get_most_recent_data(1, blockId);//get the most up-to-date data from owner, downgrading the owner state into S
                        init_tracker_HA(&D2HReqToProcess1, MESI_S);//must allocate tracker because transaction is not finished
                    }
                    else {
                        //no one owns it, no need to SnpData
                        generate_H2DResp(&D2HReqToProcess1, &H2DRespToIssue1);
                        H2DRespToIssue1.MESI_State = MESI_S;
                        H2DRespToIssue1.type = GO;
                        isIssuingH2DResp1 = 1;
                        Host.stateBitVector[blockId][0] = 0; //downgraded to shared state for everyone
                        Host.stateBitVector[blockId][1] = 1;
                        Host.existsValidCopy[blockId] = 1;
                        //TODO: also sned the data
                        H2DDataToIssue1.payload[0] = Host.dataBlocks[blockId][0];
                        H2DDataToIssue1.payload[1] = Host.dataBlocks[blockId][1];
                        isIssuingH2DData1 = 1;
                        H2DDataToIssue1.whichBlock = blockId;
                        H2DDataToIssue1.requestorCluster = D2HReqToProcess1.requestorCluster;
                        H2DDataToIssue1.requestorCore = D2HReqToProcess1.requestorCore;
                        H2DDataToIssue1.CQID = D2HReqToProcess1.CQID;
                    }
                    ;
                    break;
                case RdAny:
                    if(Host.stateBitVector[blockId][0]) {//block owned by someone, need to ask for data
                        get_most_recent_data(1, blockId);
                        init_tracker_HA(&D2HReqToProcess1, MESI_S);
                    }
                    else {//no tracker needs to be allocated, no need to ask for data
                        //no one owns the block, always giving E/M state might be too aggressive: 
                        //must invalidate all sharers. Therefore we choose to not invalidate sharers
                        //and only give E/M when no one is sharing this piece of data
                        if(!Host.existsValidCopy[blockId]) {
                            //no one has a valid copy, can give E/M state
                            generate_H2DResp(&D2HReqToProcess1, &H2DRespToIssue1);
                            H2DRespToIssue1.MESI_State = MESI_E;
                            H2DRespToIssue1.type = GO;
                            isIssuingH2DResp1 = 1;
                            Host.stateBitVector[blockId][0] = 1; //exists owner
                            Host.stateBitVector[blockId][1] = 1; //now 1 is the owner
                            Host.existsValidCopy[blockId] = 1;
                        }
                        else {
                            //no one owns it, no need to SnpData, but exists sharer(s)
                            NONPROD_ASSERT(Host.stateBitVector[blockId][2], "2 should have a copy, when exists sharers other than 1");
                            generate_H2DResp(&D2HReqToProcess1, &H2DRespToIssue1);
                            H2DRespToIssue1.MESI_State = MESI_S;
                            H2DRespToIssue1.type = GO;
                            isIssuingH2DResp1 = 1;
                            Host.stateBitVector[blockId][0] = 0; //downgraded to shared state for everyone
                            Host.stateBitVector[blockId][1] = 1; //now 1 has a copy, is therefore a sharer
                        }
                        //also send data
                        H2DDataToIssue1.payload[0] = Host.dataBlocks[blockId][0];
                        H2DDataToIssue1.payload[1] = Host.dataBlocks[blockId][1];
                        isIssuingH2DData1 = 1;
                        H2DDataToIssue1.whichBlock = blockId;
                        H2DDataToIssue1.requestorCluster = D2HReqToProcess1.requestorCluster;
                        H2DDataToIssue1.requestorCore = D2HReqToProcess1.requestorCore;
                        H2DDataToIssue1.CQID = D2HReqToProcess1.CQID;
                    }
                    ;
                    break;
                case RdCurr://TODO: need handling of this request
                    ;
                    break;
                case CleanEvict:
                    break;
                    
                default:
                    break;
            }
        }



    }

    //prevD2HReqBusy2 copy-pasted and modified once compiler errors eliminated

    if(prevD2HReqBusy2){
        printf("HA dealing with D2H req from cluster 2\n");
        //remember the block, if block under coherence transaction, postpone dealing with current D2HReq
        int blockId = D2HReqToProcess2.whichBlock;
        for(int i = 0; i < trackersCountHome; i++) {
            if(HomeTrackers[i].blockNum == blockId) {
                //delay processing if exists an ongoing transaction for same blockId
                prevD2HBlocked2 = 1;
                break;
                //Different strategies to determine next message processed by HA:
                //(a) put to process message back to D2H channel? 
                //(b) keep stalling on this message until transaction for the same block completes
                //either way, prevD2HBlocked2 signals that a message waiting to be processed is blocked
            }
        }
        if(!prevD2HBlocked2){//if the current request is not blocked (no other transaction on same block going on)
            switch(D2HReqToProcess2.type) {
                case RdOwn://TODO: add case for RdOwnNoData, and also assert Host.stateBitVector[blockId][2] != 1.
                    printf("dealing rdown (from cluster 2)\n");
                    NONPROD_ASSERT(Host.stateBitVector[blockId][0] != 1 , "Buried cache state rule: the requestor cluster should not own the block--if it does it should not need to send an ownership request to host");
                    if(Host.existsValidCopy[blockId]) {//if there exists at least one valid copy in peer caches
                        //TODO: here we assume the valid copy belongs to the other cluster.
                        //TODO: This assumption is correct because a cluster with Shared
                        //TODO: access cannot request ownership state via RdOwn, but should
                        //TODO: rather use RdOwnNoData. Need to implement RdOwnNodata clause.
                        invalidate_sharers(2, blockId);//the bitvector will be updated after SnpInv got a response from the device
                        init_tracker_HA(&D2HReqToProcess2, MESI_E);
                        if(!Host.stateBitVector[blockId][0]) {
                            //if not owned, can send data from HA now??
                            //TODO: check the meaning of Data "ordering with other transactions"
                            H2DDataToIssue2.payload[0] = Host.dataBlocks[blockId][0];
                            H2DDataToIssue2.payload[1] = Host.dataBlocks[blockId][1];
                            isIssuingD2HData2 = 1;
                            H2DDataToIssue2.whichBlock = blockId;
                            H2DDataToIssue2.requestorCluster = D2HReqToProcess2.requestorCluster;
                            H2DDataToIssue2.requestorCore = D2HReqToProcess2.requestorCore;
                            H2DDataToIssue2.CQID = D2HReqToProcess2.CQID;

                        }
                    }
                    else {
                        //There doesnt exist a valid copy
                        printf("no sharer (cluster 2)\n");
                        NONPROD_ASSERT(Host.stateBitVector[blockId][1] == 0, "no sharers anywhere, cluster 2 should not have a valid copy");
                        //the block is not shared by any caches, no tracker needs to be set up, response is sent immediately
                        generate_H2DResp(&D2HReqToProcess2, &H2DRespToIssue2);
                        H2DRespToIssue2.MESI_State = MESI_E;
                        H2DRespToIssue2.type = GO;
                        isIssuingH2DResp2 = 1;//
                        printf("Now issuing H2D response called GO\n");
                        //set onwer state in bitvector
                        Host.stateBitVector[blockId][0] = 1; //cluster 2 is going to own block
                        Host.stateBitVector[blockId][2] = 1;
                        Host.existsValidCopy[blockId] = 1; //now requestor has a valid copy
                        //TODO: also send the data
                        
                        H2DDataToIssue2.payload[0] = Host.dataBlocks[blockId][0];
                        H2DDataToIssue2.payload[1] = Host.dataBlocks[blockId][1];
                        isIssuingD2HData2 = 1;
                        H2DDataToIssue2.whichBlock = blockId;
                        H2DDataToIssue2.requestorCluster = D2HReqToProcess2.requestorCluster;
                        H2DDataToIssue2.requestorCore = D2HReqToProcess2.requestorCore;
                        H2DDataToIssue2.CQID = D2HReqToProcess2.CQID;
                    }
                    break;
                case RdShared:
                    if(Host.stateBitVector[blockId][0]) {
                        //if someone owns the block, need to get data from it
                        get_most_recent_data(1, blockId);//get the most up-to-date data from owner, downgrading the owner state into S
                        init_tracker_HA(&D2HReqToProcess2, MESI_S);//must allocate tracker because transaction is not finished
                    }
                    else {
                        //no one owns it, no need to SnpData
                        generate_H2DResp(&D2HReqToProcess2, &H2DRespToIssue2);
                        H2DRespToIssue2.MESI_State = MESI_S;
                        H2DRespToIssue2.type = GO;
                        isIssuingH2DResp1 = 1;
                        Host.stateBitVector[blockId][0] = 0; //downgraded to shared state for everyone
                        Host.stateBitVector[blockId][1] = 1;
                        Host.existsValidCopy[blockId] = 1;
                        //TODO: also sned the data
                        H2DDataToIssue2.payload[0] = Host.dataBlocks[blockId][0];
                        H2DDataToIssue2.payload[1] = Host.dataBlocks[blockId][1];
                        isIssuingD2HData2 = 1;
                        H2DDataToIssue2.whichBlock = blockId;
                        H2DDataToIssue2.requestorCluster = D2HReqToProcess2.requestorCluster;
                        H2DDataToIssue2.requestorCore = D2HReqToProcess2.requestorCore;
                        H2DDataToIssue2.CQID = D2HReqToProcess2.CQID;
                    }
                    ;
                    break;
                case RdAny:
                    if(Host.stateBitVector[blockId][0]) {//block owned by someone, need to ask for data
                        get_most_recent_data(1, blockId);
                        init_tracker_HA(&D2HReqToProcess2, MESI_S);
                    }
                    else {//no tracker needs to be allocated, no need to ask for data
                        //no one owns the block, always giving E/M state might be too aggressive: 
                        //must invalidate all sharers. Therefore we choose to not invalidate sharers
                        //and only give E/M when no one is sharing this piece of data
                        if(!Host.existsValidCopy[blockId]) {
                            //no one has a valid copy, can give E/M state
                            generate_H2DResp(&D2HReqToProcess2, &H2DRespToIssue2);
                            H2DRespToIssue2.MESI_State = MESI_E;
                            H2DRespToIssue2.type = GO;
                            isIssuingH2DResp1 = 1;
                            Host.stateBitVector[blockId][0] = 1; //exists owner
                            Host.stateBitVector[blockId][1] = 1; //now 1 is the owner
                            Host.existsValidCopy[blockId] = 1;
                        }
                        else {
                            //no one owns it, no need to SnpData, but exists sharer(s)
                            NONPROD_ASSERT(Host.stateBitVector[blockId][2], "2 should have a copy, when exists sharers other than 1");
                            generate_H2DResp(&D2HReqToProcess2, &H2DRespToIssue2);
                            H2DRespToIssue2.MESI_State = MESI_S;
                            H2DRespToIssue2.type = GO;
                            isIssuingH2DResp1 = 1;
                            Host.stateBitVector[blockId][0] = 0; //downgraded to shared state for everyone
                            Host.stateBitVector[blockId][1] = 1; //now 1 has a copy, is therefore a sharer
                        }
                        //also send data
                        H2DDataToIssue2.payload[0] = Host.dataBlocks[blockId][0];
                        H2DDataToIssue2.payload[1] = Host.dataBlocks[blockId][1];
                        isIssuingD2HData2 = 1;
                        H2DDataToIssue2.whichBlock = blockId;
                        H2DDataToIssue2.requestorCluster = D2HReqToProcess2.requestorCluster;
                        H2DDataToIssue2.requestorCore = D2HReqToProcess2.requestorCore;
                        H2DDataToIssue2.CQID = D2HReqToProcess2.CQID;
                    }
                    ;
                    break;
                case RdCurr://TODO: need handling of this request
                    ;
                    break;
                default:
                    break;
            }
        }



    }





    if(prevD2HRespBusy2) {
        //if a device has a response sent to host, need to consume that response
        //remember the block, if block under coherence transaction, postpone dealing with current D2HReq
        int blockId = D2HRespToProcess2.whichBlock;
        int trackerId = 8964;
        for(int i = 0; i < trackersCountHome; i++) {
            if(HomeTrackers[i].blockNum == blockId) {
                //delay processing if exists an ongoing transaction for same blockId
                trackerId = i;
                break;
                //Different strategies to determine next message processed by HA:
                //(a) put to process message back to D2H channel? 
                //(b) keep stalling on this message until transaction for the same block completes
                //either way, prevD2HBlocked1 signals that a message waiting to be processed is blocked
            }
        }
        switch(D2HRespToProcess2.type) {
            case RspIHitSE:
                //TODO: when no data sent, should not expect any data be sent 
                //a transaction should be complete by GO in RspXFwdY shaped msgs
                generate_H2DResp_from_tracker(&HomeTrackers[trackerId], &H2DRespToIssue1);
                isIssuingH2DResp1 = 1;
                if(Host.stateBitVector[blockId][0]) {
                    NONPROD_ASSERT(Host.stateBitVector[blockId][0] == 2, "owner bit should be kept set to cluster 2 before cluster 2 response is processed");
                    //if the D2HResp sender was owner, RspIHitSE indicates no data will be forwarded
                    //need host to send data instead (because responder was in E state, which is clean)
                    //TODO: send data
                    //commented this below line because RspIHitSE indicates 
                    //no data shall be sent
                    //generate_H2DData_from_HA(&H2DDataToIssue1, blockId, &H2DRespToIssue1);
                    
                    isIssuingH2DData1 = 1;
                    //TODO: set bitvector
                    
                }
                if(H2DRespToIssue1.MESI_State == MESI_E || H2DRespToIssue1.MESI_State == MESI_M) {
                    Host.stateBitVector[blockId][0] = 1; //change owner to cluster 1
                }
                else {
                    Host.stateBitVector[blockId][0] = 0; //no one is owner now: 1 is not, 2 has been downgraded
                }
                Host.stateBitVector[blockId][1] = 1; //cluster1 has a valid copy now
                Host.stateBitVector[blockId][2] = 0; //cluster2 has become invalid now
                Host.existsValidCopy[blockId] = 1;
                if(HomeTrackers[trackerId].DataArrivedBeforeGO) {//data + response both arrived for the snoop,
                    //no need for host to keep the tracker, transaction complete from host's pov
                    deallocate_tracker(trackerId);
                }
                else {
                    //2 to indicate data has not arrived yet, GO is sent first
                    HomeTrackers[trackerId].DataArrivedBeforeGO = 2;
                }
                break;
            case RspSHitSE:
                
                break;
            case RspIFwdM: 
                printf("RspIFwdM response received from device 2. TrackerId is %d\n", trackerId);
                generate_H2DResp_from_tracker(&HomeTrackers[trackerId], &H2DRespToIssue1);
                isIssuingH2DResp1 = 1;
                if(Host.stateBitVector[blockId][0]) {
                    printf("state bit vector 0 is non-zero\n");
                    NONPROD_ASSERT(Host.stateBitVector[blockId][0] == 2, "owner bit should be kept set to cluster 2 before cluster 2 response is processed");
                    //if the D2HResp sender was owner, RspIHitSE indicates no data will be forwarded
                    //need host to send data instead (because responder was in E state, which is clean)
                    //TODO: send data
                    // generate_H2DData_from_HA(&H2DDataToIssue1, blockId, &H2DRespToIssue1);
                    // isIssuingH2DData1 = 1;
                    //TODO: set bitvector
                    
                }
                if(H2DRespToIssue1.MESI_State == MESI_E || H2DRespToIssue1.MESI_State == MESI_M) {
                    printf("cluster 1 granted ownership of block %d\n", blockId);
                    Host.stateBitVector[blockId][0] = 1; //change owner to cluster 1
                }
                else {
                    Host.stateBitVector[blockId][0] = 0; //no one is owner now: 1 is not, 2 has been downgraded
                }
                Host.stateBitVector[blockId][1] = 1; //cluster1 has a valid copy now
                Host.stateBitVector[blockId][2] = 0; //cluster2 has become invalid now
                Host.existsValidCopy[blockId] = 1;
                if(HomeTrackers[trackerId].DataArrivedBeforeGO) {//data + response both arrived for the snoop,
                    //no need for host to keep the tracker, transaction complete from host's pov
                    deallocate_tracker(trackerId);
                }
                else {
                    //2 to indicate data has not arrived yet, GO is sent first
                    //TODO: When no data, no need for sending data and this logic
                    printf("Data arrives after GO\n");
                    HomeTrackers[trackerId].DataArrivedBeforeGO = 2;
                }
                break;
            default:
                break;


        }


        


    
    }



    if(prevD2HDataBusy2) {
        //if previous cycle some D2H data was on the channel, now take into host
        //and send to the right requestor cluster
        printf("payloads:[%d], [%d]\n", D2HDataToProcess2.payload[0], D2HDataToProcess2.payload[1]);
        isIssuingH2DData1 = 1;
        H2DDataToIssue1.CQID = D2HDataToProcess2.UQID;
        H2DDataToIssue1.payload[0] = D2HDataToProcess2.payload[0];
        H2DDataToIssue1.payload[1] = D2HDataToProcess2.payload[1];
        H2DDataToIssue1.requestorCluster = D2HDataToProcess2.requestorCluster;
        H2DDataToIssue1.requestorCore = D2HDataToProcess2.requestorCore;
        H2DDataToIssue1.whichBlock = D2HDataToProcess2.whichBlock;        
        

    }




}




//suppose cluster 1 has X in shared state, cluster 2 has Y in shared state.
//now 1 wants Y in modified state, 2 wants X in modified state. Both sends GetM to host, and was translated
//into RdOwn to the host, host sends SnpInv to both parties. If 1 and 2 are AT, 1 would stall host's request
//for X, because it was on a transaction for Y, and only deals with other requests once Y's completed
//But it cannot get Y, because cluster 2 is not sending Y unless cluster 1 sends X

void DCOH_acts(Cluster * cluster, int id) {
    //device agent translates cluster's own bus message to CXL messages, ready to be put into D2H channels
    if(id == 1) {  
        printf("dcoh of cluster 1 acting, %d, %d, %d\n", prevH2DRespBusy1, prevH2DDataBusy1, prevH2DReqBusy1);
        //first process 3 channels' messages: H2D response, H2D data, H2D request
        if(prevH2DRespBusy1) {//if need to process an H2D response
            printf("need to consume response from host\n");
            switch(H2DRespToProcess1.type) {
                case GO:
                    printf("GO clause activated\n");
                    cluster->isIssuingResponse = 1;
                    cluster->response.External = 1;
                    cluster->response.payload[0] = 89; //GO does not carry data, these are just paddings
                    cluster->response.payload[1] = 64;
                    cluster->response.receiver = H2DRespToProcess1.requestorCore;
                    cluster->response.sender = 8964;
                    cluster->response.toMem = 0;
                    cluster->response.type = GO_CXL;
                    cluster->response.fromHA = 1;
                    cluster->response.whichBlock = H2DRespToProcess1.whichBlock;
                    //register block/cacheline state in this cluster (1)
                    DCOH1[H2DRespToProcess1.whichBlock] = H2DRespToProcess1.MESI_State;

                    break;
                case WritePull:
                    break;
                default:
                    break;
                    //if(H2DRespToProcess1.MESI_State == MESI_E || H2DRespToProcess1.MESI_State == MESI_M) {
                    
            }


            //break; //stop dealing with other channel messages if dealt with current message


        }
        if(prevH2DDataBusy1) { 
            //if already need to put something on bus, need to wait for next cycle to process Data
            if(cluster->isIssuingResponse) {
                prevH2DDataBlocked1 = 1;
            }
            else {
                printf("consuming h2d data \n");

                cluster->isIssuingResponse = 1;
                cluster->response.External = 1;
                cluster->response.payload[0] = H2DDataToProcess1.payload[0];
                cluster->response.payload[1] = H2DDataToProcess1.payload[1];
                cluster->response.receiver = H2DDataToProcess1.requestorCore;
                cluster->response.sender = 8964; //can be any number, External = 1 indicates it is from HA
                cluster->response.toMem = 0; //only cached at core's caches, llc/mem is private for cluster itself
                //TODO: make sure H2D Data is translated into the right type (i.e. Data, not GO_CXL)
                cluster->response.type = Data; 
                cluster->response.whichBlock = H2DDataToProcess1.whichBlock;
                printf("payl1 %d, payl2 %d\n", cluster->response.payload[0], cluster->response.payload[1]);

                printf("cluster->response.whichBlock is %d\n", cluster->response.whichBlock);
                //TODO: actual place prevH2DDataBlocked1 should be set to 0:
                //after cluster transaction completes. Rather than here:
                prevH2DDataBlocked1 = 0;
                //H2D Data was received and taken into cluster. it still takes time
                //for the data to arrive into the core.
            }

            //break;
        }
        


        if(prevH2DReqBusy1) {
            
            //one possible deadlock scenario: host sends request for block Y,
            //but cluster transaction in progress for block X. So DA blocks the request for Y until
            //transaction for X completes. The other cluster is in the same situation, except the
            //request it blocks was for X, and the response it needs for Y.
            //Therefore we should allow another transaction breaking into the current transaction
            if(cluster->transactionInProgress) {//if cluster already dealing with a coherence request,
                //cannot deal with this coherence request
                prevH2DReqBlocked1 = 1;
            }
            else {
                //if()
                cluster->isIssuingRequest = 1;
                cluster->request.External = 1;
                cluster->request.receiver = 8964;//host doesn't know which core has the block. it only knows which cluster has it.
                cluster->request.sender = H2DReqToProcess1.requestorCluster; //here sender indicates cluster not core
                cluster->request.toMem = 0;
                cluster->request.fromHA = 1; //msg flowing from HA to cluster
                TempTracker1.snoopType = H2DReqToProcess1.type;
                TempTracker1.UQID = H2DReqToProcess1.UQID;

                isIssuingD2HData1 = 1;
                
                TempTracker1.cachelineTypeBeforeSnoop = DCOH1[H2DReqToProcess1.whichBlock];//
                
                TempTracker1.requestorCluster = H2DReqToProcess1.requestorCluster;
                TempTracker1.requestorCore = H2DReqToProcess1.requestorCore;
                switch(H2DReqToProcess1.type) {
                case SnpInv:
                    cluster->request.type = GetM;
                    break;
                case SnpData:
                    cluster->request.type = GetS;
                    break;
                case SnpCurr:
                    //???
                    cluster->request.type = GetCurrent;
                    break;
                default:
                    break;
                }
                    
                cluster->request.whichBlock = H2DReqToProcess1.whichBlock;
                prevH2DReqBlocked1 = 0;
                
            }
            
            
        }

        

        

        //DA reacting to ineternal bus messages, translating into channel D2H msgs
        int blockId = cluster->snooping_bus.whichBlock;
        //DA reacting to internal bus messages, if bus is not idle,  and message is external, flowing towards HA
        //for example, if a bus message was from HA and translated by Dcoh already, no need to process again
        if(cluster->snooping_bus.type == Idle || !(cluster->snooping_bus.External) || (cluster->snooping_bus.fromHA)) {
            printf("Idle: %d, External: %d, fromHA %d\n", cluster->snooping_bus.type, cluster->snooping_bus.External, cluster->snooping_bus.fromHA);
            return; //DA only acts if bus message is external message, and the message is flowing from cluster to HA, not from HA
        } 
        if(cluster->snooping_bus.receiver == 1 || cluster->snooping_bus.receiver == 2){
            //TODO: check all messages receiver 1 or 2 indicate intra-cluster messages
            //message definitely for host, not other core within cluster
            printf("returned 2\n");
            return; //when cluster has high privilige access, resolve internal coherence messages within cluster, no need to notify host
        }
        //deal with message on snooping bus
        switch(cluster->snooping_bus.type) {
            case GetS:
                
                if(DCOH1[blockId] != MESI_I)
                    break;
                //
                isIssuingD2HReq1 = 1;
                D2HReqToIssue1.type = RdShared;
                D2HReqToIssue1.requestorCluster = id;
                D2HReqToIssue1.requestorCore = cluster->snooping_bus.sender;
                D2HReqToIssue1.whichBlock = cluster->snooping_bus.whichBlock;
                D2HReqToIssue1.CQID = CQID_counter;
                D2HReqToIssue1.DataArrivedBeforeGO = 0;


                //allocate tracker at DA
                cluster1Trackers[trackersCount1].CQID = CQID_counter;
                CQID_counter++;
                cluster1Trackers[trackersCount1].blockNum = cluster->snooping_bus.whichBlock;
                cluster1Trackers[trackersCount1].DataArrivedBeforeGO = 0;
                cluster1Trackers[trackersCount1].requestorCluster = id;
                cluster1Trackers[trackersCount1].requestorCore = cluster->snooping_bus.sender;
                trackersCount1++;

                break;
            case GetM:
                if(DCOH1[blockId] == MESI_E || DCOH1[blockId] == MESI_M)
                    break;
                printf("DCOH dealing with bus message GetM\n");
                isIssuingD2HReq1 = 1;
                D2HReqToIssue1.type = RdOwn;
                D2HReqToIssue1.requestorCluster = id;
                D2HReqToIssue1.requestorCore = cluster->snooping_bus.sender;
                D2HReqToIssue1.whichBlock = cluster->snooping_bus.whichBlock;
                D2HReqToIssue1.CQID = CQID_counter;
                D2HReqToIssue1.DataArrivedBeforeGO = 0;
                //allocate tracker at DA
                cluster1Trackers[trackersCount1].CQID = CQID_counter;
                CQID_counter++;
                cluster1Trackers[trackersCount1].blockNum = cluster->snooping_bus.whichBlock;
                cluster1Trackers[trackersCount1].DataArrivedBeforeGO = 0;
                cluster1Trackers[trackersCount1].requestorCluster = id;
                cluster1Trackers[trackersCount1].requestorCore = cluster->snooping_bus.sender;
                trackersCount1++;
                            
                break;
            case Data:
                
                printf("d2h data from data to host sent at internal bus 1\n");
                //two things to issue: data and response. On a separate channel.
                isIssuingD2HData1 = 1;
                // int trackerId = 8964;
                // for(int i = 0; i <= trackersCount1 - 1; i++ ) {
                //     if(cluster1Trackers[i].blockNum == cluster->snooping_bus.whichBlock) {
                //         trackerId = i;
                //         break;
                //     }
                // }
                // NONPROD_ASSERT(trackerId != 8964, "a tracker should have been allocated");
                //TODO: make sure a tracker was allocated at beginning of an external coherence transaction (request from HA)
                D2HDataToIssue1.UQID = TempTracker1.UQID;
                D2HDataToIssue1.payload[0] = cluster->snooping_bus.payload[0];
                D2HDataToIssue1.payload[1] = cluster->snooping_bus.payload[1];
                D2HDataToIssue1.requestorCluster = TempTracker1.requestorCluster;
                D2HDataToIssue1.requestorCore = TempTracker1.requestorCore;

                isIssuingD2HResp1 = 1;
                D2HRespToIssue1.CQID = TempTracker1.UQID;
                D2HRespToIssue1.requestorCluster = D2HDataToIssue1.requestorCluster;
                D2HRespToIssue1.requestorCore = D2HDataToIssue1.requestorCore;
                D2HRespToIssue1.whichBlock = cluster->snooping_bus.whichBlock;
                switch(TempTracker1.cachelineTypeBeforeSnoop) {
                    case MESI_I:
                        //was hit in invalid state, no data should be sent
                        D2HRespToIssue1.type = RspIHitI;
                        isIssuingD2HData1 = 0;
                        break;
                    case MESI_S:
                        switch (TempTracker1.snoopType)
                        {
                        case SnpCurr:
                            D2HRespToIssue1.type = RspVFwdV;
                            //current data is being sent.
                            break;
                        case SnpData:
                            D2HRespToIssue1.type = RspSHitSE;
                            isIssuingD2HData1 = 0;
                            
                            break;
                        case SnpInv:
                            D2HRespToIssue1.type = RspIHitSE;
                            break;
                        
                        default:
                            break;
                        }
                        break;
                    case MESI_M:
                        switch (TempTracker1.snoopType)
                        {
                        case SnpCurr:
                            D2HRespToIssue1.type = RspVFwdV;
                            //current data is sent.
                            break;
                        case SnpData:
                            D2HRespToIssue1.type = RspSFwdM;
                            //TODO: RspIFwdM is also allowed, but not sure why and use case
                            break;
                        case SnpInv:
                            D2HRespToIssue1.type = RspIFwdM;
                            break;
                        
                        default:
                            break;
                        }
                        break;
                    case MESI_E:
                        switch (TempTracker1.snoopType)
                        {
                        case SnpCurr:
                            D2HRespToIssue1.type = RspVFwdV;
                            //current data is sent.
                            break;
                        case SnpData:
                            D2HRespToIssue1.type = RspSFwdM;
                            //TODO: RspIFwdM is also allowed, but not sure why and use case
                            break;
                        case SnpInv:
                            D2HRespToIssue1.type = RspIFwdM;
                            break;
                        
                        default:
                            break;
                        }
                        break;
                    default:
                        break;
                        
                }
                

                

            default:
                break;


        }

    }


    if(id == 2) {  
        printf("dcoh of cluster 2 acting, %d, %d, %d\n", prevH2DRespBusy2, prevH2DDataBusy2, prevH2DReqBusy2);
        //first process 3 channels' messages: H2D response, H2D data, H2D request
        if(prevH2DRespBusy2) {//if need to process an H2D response
            printf("need to consume response from host\n");
            switch(H2DRespToProcess2.type) {
                case GO:
                    printf("GO clause activated\n");
                    cluster->isIssuingResponse = 1;
                    cluster->response.External = 1;
                    cluster->response.payload[0] = 89; //GO does not carry data, these are just paddings
                    cluster->response.payload[1] = 64;
                    cluster->response.receiver = H2DRespToProcess2.requestorCore;
                    cluster->response.sender = 8964;
                    cluster->response.toMem = 0;
                    cluster->response.type = GO_CXL;
                    cluster->response.fromHA = 1;
                    cluster->response.whichBlock = H2DRespToProcess2.whichBlock;

                    DCOH2[H2DRespToProcess2.whichBlock] = H2DRespToProcess2.MESI_State;

                    break;
                case WritePull:
                    break;
                default:
                    break;
                    //if(H2DRespToProcess2.MESI_State == MESI_E || H2DRespToProcess2.MESI_State == MESI_M) {
                    
            }


            //break; //stop dealing with other channel messages if dealt with current message


        }
        if(prevH2DDataBusy2) { 
            //if already need to put something on bus, need to wait for next cycle to process Data
            if(cluster->isIssuingResponse) {
                prevH2DDataBlocked2 = 1;
            }
            else {
                printf("consuming h2d data \n");

                cluster->isIssuingResponse = 1;
                cluster->response.External = 1;
                cluster->response.payload[0] = H2DDataToProcess2.payload[0];
                cluster->response.payload[1] = H2DDataToProcess2.payload[1];
                cluster->response.receiver = H2DDataToProcess2.requestorCore;
                cluster->response.sender = 8964; //can be any number, External = 1 indicates it is from HA
                cluster->response.toMem = 0; //only cached at core's caches, llc/mem is private for cluster itself
                //TODO: make sure H2D Data is translated into the right type (i.e. Data, not GO_CXL)
                cluster->response.type = Data; 
                cluster->response.whichBlock = H2DDataToProcess2.whichBlock;
                prevH2DDataBlocked2 = 0;
            }

            //break;
        }


        if(prevH2DReqBusy2) {
            printf("dcoh2 reacting to H2D request\n");
            //one possible deadlock scenario: host sends request for block Y,
            //but cluster transaction in progress for block X. So DA blocks the request for Y until
            //transaction for X completes. The other cluster is in the same situation, except the
            //request it blocks was for X, and the response it needs for Y.
            //Therefore we should allow another transaction breaking into the current transaction
            if(cluster->transactionInProgress) {//if cluster already dealing with a coherence request,
                //cannot deal with this coherence request
                printf("trans in prog\n");
                prevH2DReqBlocked2 = 1;
            }
            else {
                //if()
                printf("trans not inprog\n");
                cluster->isIssuingRequest = 1;
                cluster->request.External = 1;
                cluster->request.receiver = 8964;//host doesn't know which core has the block. it only knows which cluster has it.
                cluster->request.sender = H2DReqToProcess2.requestorCluster; //here sender indicates cluster not core
                cluster->request.toMem = 0;
                cluster->request.fromHA = 1; //msg flowing from HA to cluster
                TempTracker2.snoopType = H2DReqToProcess2.type;
                TempTracker2.cachelineTypeBeforeSnoop = DCOH2[H2DReqToProcess2.whichBlock];
                TempTracker2.UQID = H2DReqToProcess2.UQID;
                TempTracker2.requestorCluster = H2DReqToProcess2.requestorCluster;
                TempTracker2.requestorCore = H2DReqToProcess2.requestorCore;
                if(H2DReqToProcess2.type == SnpInv){
                    printf("GetM needed for SnpInv\n");
                    cluster->request.type = GetM;
                }
                else {
                    cluster->request.type = GetS;

                }
                cluster->request.whichBlock = H2DReqToProcess2.whichBlock;
                prevH2DReqBlocked2 = 0;
                
            }
            
            
        }

        


        int blockId = cluster->snooping_bus.whichBlock;
        //DA reacting to internal bus messages, if bus is not idle,  and message is external, flowing towards HA
        //for example, if a bus message was from HA and translated by Dcoh already, no need to process again
        if(cluster->snooping_bus.type == Idle || !(cluster->snooping_bus.External) || (cluster->snooping_bus.fromHA)) {
            printf("Idle: %d, External: %d, fromHA %d\n", cluster->snooping_bus.type, cluster->snooping_bus.External, cluster->snooping_bus.fromHA);
            return; //DA only acts if bus message is external message, and the message is flowing from cluster to HA, not from HA
        } 
        if(cluster->snooping_bus.receiver == 1 || cluster->snooping_bus.receiver == 2){ //message needs to be sent to host, 3 indicates that. 
            //1-->core 1, 2----> core2, 3----> dcoh
            printf("returned2\n");
            return; //when cluster has high privilige access, resolve internal coherence messages within cluster, no need to notify host

        }
        //deal with message on snooping bus
        switch(cluster->snooping_bus.type) {
            case GetS:
                
                //if the DCOH registers cache state in privilege higher than or equal to 
                //coherence request, then resolve coherence within cluster, no need for
                //DCOH to generate messages on D2H channels
                if(DCOH2[blockId] != MESI_I)
                    break;
                
                isIssuingD2HReq2 = 1;
                D2HReqToIssue2.type = RdShared;
                D2HReqToIssue2.requestorCluster = id;
                D2HReqToIssue2.requestorCore = cluster->snooping_bus.sender;
                D2HReqToIssue2.whichBlock = cluster->snooping_bus.whichBlock;
                D2HReqToIssue2.CQID = CQID_counter;
                D2HReqToIssue2.DataArrivedBeforeGO = 0;
                //allocate tracker at DA
                cluster2Trackers[trackersCount2].CQID = CQID_counter;
                CQID_counter++;
                cluster2Trackers[trackersCount2].blockNum = cluster->snooping_bus.whichBlock;
                cluster2Trackers[trackersCount2].DataArrivedBeforeGO = 0;
                cluster2Trackers[trackersCount2].requestorCluster = id;
                cluster2Trackers[trackersCount2].requestorCore = cluster->snooping_bus.sender;
                trackersCount2++;

                break;
            case GetM:
                if(DCOH2[blockId] == MESI_E || DCOH2[blockId] == MESI_M)
                    break;
                printf("DCOH dealing with bus message GetM\n");
                isIssuingD2HReq2 = 1;
                D2HReqToIssue2.type = RdOwn;
                D2HReqToIssue2.requestorCluster = id;
                D2HReqToIssue2.requestorCore = cluster->snooping_bus.sender;
                D2HReqToIssue2.whichBlock = cluster->snooping_bus.whichBlock;
                D2HReqToIssue2.CQID = CQID_counter;
                D2HReqToIssue2.DataArrivedBeforeGO = 0;
                //allocate tracker at DA
                cluster2Trackers[trackersCount2].CQID = CQID_counter;
                CQID_counter++;
                cluster2Trackers[trackersCount2].blockNum = cluster->snooping_bus.whichBlock;
                cluster2Trackers[trackersCount2].DataArrivedBeforeGO = 0;
                cluster2Trackers[trackersCount2].requestorCluster = id;
                cluster2Trackers[trackersCount2].requestorCore = cluster->snooping_bus.sender;
                trackersCount2++;
                            
                break;
            case Data:
                printf("d2h data from data to host sent at internal bus 2\n");
                //two things to issue: data and response. On a separate channel.
                isIssuingD2HData2 = 1;
                // int trackerId = 8964;
                // for(int i = 0; i <= trackersCount2 - 1; i++ ) {
                //     if(cluster2Trackers[i].blockNum == cluster->snooping_bus.whichBlock) {
                //         trackerId = i;
                //         break;
                //     }
                // }
                // NONPROD_ASSERT(trackerId != 8964, "a tracker should have been allocated");
                //TODO: make sure a tracker was allocated at beginning of an external coherence transaction (request from HA)
                D2HDataToIssue2.UQID = TempTracker2.UQID;
                D2HDataToIssue2.payload[0] = cluster->snooping_bus.payload[0];
                D2HDataToIssue2.payload[1] = cluster->snooping_bus.payload[1];
                
                D2HDataToIssue2.requestorCluster =   TempTracker2.requestorCluster;
                D2HDataToIssue2.requestorCore = TempTracker2.requestorCore;
                D2HDataToIssue2.whichBlock = cluster->snooping_bus.whichBlock;

                isIssuingD2HResp2 = 1;
                D2HRespToIssue2.CQID = TempTracker2.UQID;
                D2HRespToIssue2.requestorCluster = D2HDataToIssue2.requestorCluster;
                D2HRespToIssue2.requestorCore = D2HDataToIssue2.requestorCore;
                D2HRespToIssue2.whichBlock = cluster->snooping_bus.whichBlock;
                switch(TempTracker2.cachelineTypeBeforeSnoop) {
                    case MESI_I:
                        //was hit in invalid state, no data should be sent
                        D2HRespToIssue2.type = RspIHitI;
                        isIssuingD2HData2 = 0;
                        break;
                    case MESI_S:
                        switch (TempTracker2.snoopType)
                        {
                        case SnpCurr:
                            D2HRespToIssue2.type = RspVFwdV;
                            //current data is being sent.
                            break;
                        case SnpData:
                            D2HRespToIssue2.type = RspSHitSE;
                            isIssuingD2HData2 = 0;
                            
                            break;
                        case SnpInv:
                            D2HRespToIssue2.type = RspIHitSE;
                            isIssuingD2HData2 = 0;
                            break;
                        
                        default:
                            break;
                        }
                        break;
                    case MESI_M:
                        switch (TempTracker2.snoopType)
                        {
                        case SnpCurr:
                            D2HRespToIssue2.type = RspVFwdV;
                            //current data is sent.
                            break;
                        case SnpData:
                            D2HRespToIssue2.type = RspSFwdM;
                            //TODO: RspIFwdM is also allowed, but not sure why and use case
                            break;
                        case SnpInv:
                            printf("should hit SnpInv+M branch for test2, blockId is %d\n", D2HRespToIssue2.whichBlock);
                            D2HRespToIssue2.type = RspIFwdM;
                            break;
                        
                        default:
                            break;
                        }
                        break;
                    case MESI_E:
                        switch (TempTracker2.snoopType)
                        {
                        case SnpCurr:
                            D2HRespToIssue2.type = RspVFwdV;
                            //current data is sent.
                            break;
                        case SnpData:
                            D2HRespToIssue2.type = RspSFwdM;
                            //TODO: RspIFwdM is also allowed, but not sure why and use case
                            break;
                        case SnpInv:
                            D2HRespToIssue2.type = RspIFwdM;
                            break;
                        
                        default:
                            break;
                        }
                        break;
                    default:
                        break;
                        
                }
                

                

            default:
                break;


        }


    }


}

void decide_DCOH_to_process_messages(int id) {

    if(id == 1) {
        if(H2DReq1Counter > 0 && !prevH2DReqBlocked1) {
            //TODO: nondet choose one of the H2D requests
            H2DReqToProcess1 = H2DReq1[0];
            prevH2DReqBusy1 = 1;
            for(int i = 0; i < H2DReq1Counter - 1; i++) {
                H2DReq1[i] = H2DReq1[i + 1];
            }
            H2DReq1Counter--;
        }
        else if (prevH2DReqBlocked1) {//TODO: also need a variable prevD2Hblocked for host?
            ;//cannot process more requests, current request still awaiting so stays busy
        }
        else {
            prevH2DReqBusy1 = 0;
        } 
    }
    else {
        
        if(H2DReq2Counter > 0 && !prevH2DReqBlocked2) {
            
            H2DReqToProcess2 = H2DReq2[0];
            prevH2DReqBusy2 = 1;
            for(int i = 0; i < H2DReq2Counter - 1; i++) {
                H2DReq2[i] = H2DReq2[i + 1];
            }
            H2DReq2Counter--;
        }
        else if(prevH2DReqBlocked2) {
            ;
        }
        else {
            prevH2DReqBusy2 = 0;
        }

    }       
    
    



    //taking H2D response from channel to buffer for host to consume
    if(id == 1) {
        if(H2DResp1Counter > 0) {
            //TODO: nondet choose one of the H2D Respuests
            
            H2DRespToProcess1 = H2DResp1[0];
            prevH2DRespBusy1 = 1;
            for(int i = 0; i < H2DResp1Counter - 1; i++) {
                H2DResp1[i] = H2DResp1[i + 1];
            }
            H2DResp1Counter--;
        }
        else {
            prevH2DRespBusy1 = 0;
        }
    }

    else {
        if(H2DResp2Counter > 0) {
            printf("h2d response in channel to process\n");
            //TODO: nondet choose one of the H2D Respuests
            H2DRespToProcess2 = H2DResp2[0];
            prevH2DRespBusy2 = 1;
            for(int i = 0; i < H2DResp2Counter - 1; i++) {
                H2DResp2[i] = H2DResp2[i + 1];
            }
            H2DResp2Counter--;
        }
        else {
            prevH2DRespBusy2 = 0;
        }
    }


    // if(id == 1) {
    //     if(H2DData1Counter > 0) {
    //         printf("h2d data received\n");
    //         H2DDataToProcess1 = H2DData1[0];
    //         prevH2DDataBusy1 = 1;
    //         for(int i = 0; i < H2DData1Counter - 1; i++) {
    //             H2DData1[i] = H2DData1[i + 1];
    //         }
    //         H2DData1Counter--;
    //     }
    //     else {
    //         prevH2DDataBusy1 = 0;
    //     }
    
    // }
    // //taking H2D data from channel to buffer for host to consume
    // else {
    //     if(H2DData2Counter > 0) {
    //         H2DDataToProcess2 = H2DData2[0];
    //         prevH2DDataBusy2 = 1;
    //         for(int i = 0; i < H2DData2Counter - 1; i++) {
    //             H2DData2[i] = H2DData2[i + 1];
    //         }
    //         H2DData2Counter--;
    //     }
    //     else {
    //         prevH2DDataBusy2 = 0;
    //     }
    // }




    if(id == 1) {
        if(H2DData1Counter > 0 && !prevH2DDataBlocked1) {
            //TODO: nondet choose one of the H2D requests
            H2DDataToProcess1 = H2DData1[0];
            prevH2DDataBusy1 = 1;
            for(int i = 0; i < H2DData1Counter - 1; i++) {
                H2DData1[i] = H2DData1[i + 1];
            }
            H2DData1Counter--;
        }
        else if (prevH2DDataBlocked1) {
            ;//cannot process more data, current data still awaiting so stays busy
        }
        else {
            prevH2DDataBusy1 = 0;
        } 
    }
    else {
        if(H2DData2Counter > 0 && !prevH2DDataBlocked2) {
            H2DDataToProcess2 = H2DData2[0];
            prevH2DDataBusy2 = 1;
            for(int i = 0; i < H2DData2Counter - 1; i++) {
                H2DData2[i] = H2DData2[i + 1];
            }
            H2DData2Counter--;
        }
        else if(prevH2DDataBlocked2) {
            ;
        }
        else {
            prevH2DDataBusy2 = 0;
        }

    }  



}

//want to check:


void cluster_acts(Cluster * cluster, int id) {
    int clusterInternalInstructionsFinished = 0;
    if(cluster->program1.PC >= cluster->program1.NumInstructions && cluster->program2.PC >= cluster->program2.NumInstructions && !cluster->core1.Stalled && !cluster->core2.Stalled && !cluster->transactionInProgress){
        clusterInternalInstructionsFinished = 1;
    }
    if(clusterInternalInstructionsFinished && cluster->previousBusMsg.type == Idle){
        ;//do nothing if all internal instructions done, and nothing on bus to react to
    }
    else {//TODO: cores react only if all internal instructions have been finished 
        // printf("follow1 %d, cluster->program1.PC: %d, cluster->program1.NumInstructions: %d\n", cluster, cluster->program1.PC, cluster->program1.NumInstructions);
        cores_react(cluster);
    }

    // if(cluster->previousBusMsg.type == Data)
    //     printf("Data on bus before DCOH acts\n");
    // printf("a %d %d\n", globalCounter, cluster->cycle);
    
    DCOH_acts(cluster, id); //device agent deals with bus/channel messages (from previous cycle)
    // printf("b %d %d\n", globalCounter, cluster->cycle);

    //this doesn't need to be in the exact location here, as long as the internal side logic is executed (otherwise the message we want to react on will be overwritten)
    //before save_current_msg_for_next_cycle, and the HA side logic executed before decide_DCOH_to_process_messages (same reason)
    if(!clusterInternalInstructionsFinished){
        mem_react(cluster);
    }
    save_current_msg_for_next_cycle(cluster);
    update_bus_msg_for_next_cycle(cluster);
    //printf("id: %d\n", id);
    decide_DCOH_to_process_messages(id);//in particular, HA side, not internal side


    cluster->cycle++;
}
int all_clusters_finished(Cluster * cl1, Cluster * cl2) {
    int finishedCounter = 0;
    printf("cl1 PC1 %d, PC2: %d\n", cl1->program1.PC, cl1->program2.PC);
    printf("cl2 PC1 %d, PC2: %d\n", cl2->program1.PC, cl2->program2.PC);
    printf("cl1 NumInstrs 1 %d, NumInstrs2: %d\n", cl1->program1.NumInstructions, cl1->program2.NumInstructions);
    printf("cl2 NumInstrs 1 %d, NumInstrs2: %d\n", cl2->program1.NumInstructions, cl2->program2.NumInstructions);
    
    if(cl1->program1.PC >= cl1->program1.NumInstructions && cl1->program2.PC >= cl1->program2.NumInstructions && !cl1->core1.Stalled && !cl1->core2.Stalled && !cl1->transactionInProgress)
        finishedCounter++;
    if(cl2->program1.PC >= cl2->program1.NumInstructions && cl2->program2.PC >= cl2->program2.NumInstructions && !cl2->core1.Stalled && !cl2->core2.Stalled && !cl2->transactionInProgress)
        finishedCounter++;
    if(finishedCounter >= 2)
        return 1;
    else 
        return 0;
}
void decide_HA_to_process_messages() {
    //taking D2H request from channel to buffer for host to process
    if(prevD2HBlocked1) {// Current implementation: keep stalling, alternative possible.
        ;
    }
    else {
        if(D2HReq1Counter > 0) {
            //TODO: nondet choose one of the D2H requests
            D2HReqToProcess1 = D2HReq1[0];
            prevD2HReqBusy1 = 1;
            for(int i = 0; i < D2HReq1Counter - 1; i++) {
                D2HReq1[i] = D2HReq1[i + 1];
            }
            D2HReq1Counter--;
        }
        else {
            prevD2HReqBusy1 = 0;
        }        
    }
    if(prevD2HBlocked2) {// Current implementation: keep stalling, alternative possible.
        ;
    }
    else {
        if(D2HReq2Counter > 0) {
            D2HReqToProcess2 = D2HReq2[0];
            prevD2HReqBusy2 = 1;
            for(int i = 0; i < D2HReq2Counter - 1; i++) {
                D2HReq2[i] = D2HReq2[i + 1];
            }
            D2HReq2Counter--;
        }
        else {
            prevD2HReqBusy2 = 0;
        }
    }



    //taking D2H response from channel to buffer for host to consume
    if(D2HResp1Counter > 0) {
        //TODO: nondet choose one of the D2H Respuests
        D2HRespToProcess1 = D2HResp1[0];
        prevD2HRespBusy1 = 1;
        for(int i = 0; i < D2HResp1Counter - 1; i++) {
            D2HResp1[i] = D2HResp1[i + 1];
        }
        D2HResp1Counter--;
    }
    else {
        prevD2HRespBusy1 = 0;
    }

    if(D2HResp2Counter > 0) {
        printf("d2h resp sent from channel into host buffer\n");
        //TODO: nondet choose one of the D2H Respuests
        D2HRespToProcess2 = D2HResp2[0];
        prevD2HRespBusy2 = 1;
        for(int i = 0; i < D2HResp2Counter - 1; i++) {
            D2HResp2[i] = D2HResp2[i + 1];
        }
        D2HResp2Counter--;
    }
    else {
        prevD2HRespBusy2 = 0;
    }


    //taking D2H data from channel to buffer for host to consume
    if(D2HData1Counter > 0) {
        D2HDataToProcess1 = D2HData1[0];
        prevD2HDataBusy1 = 1;
        for(int i = 0; i < D2HData1Counter - 1; i++) {
            D2HData1[i] = D2HData1[i + 1];
        }
        D2HData1Counter--;
    }
    else {
        prevD2HDataBusy1 = 0;
    }
    
    if(D2HData2Counter > 0) {
        D2HDataToProcess2 = D2HData2[0];
        prevD2HDataBusy2 = 1;
        for(int i = 0; i < D2HData2Counter - 1; i++) {
            D2HData2[i] = D2HData2[i + 1];
        }
        D2HData2Counter--;
    }
    else {
        prevD2HDataBusy2 = 0;
    }

    

}
void update_cache_channels_messages() {
    //for all clusters i = 1, 2, do: take every toIssue msg (if there is one) and put into channel
    //reset the hasMsgToIssue signal to 0
    //assumes that no overflow occurs on any channel
    if(isIssuingH2DData1) {
        printf("Now sending data to cluster 1 from host\n");
        H2DData1[H2DData1Counter] = H2DDataToIssue1;
        H2DData1Counter++;
        isIssuingH2DData1 = 0;
    }
    if(isIssuingH2DData2) {
        H2DData2[H2DData2Counter] = H2DDataToIssue2;
        H2DData2Counter++;
        isIssuingH2DData2 = 0;
    }
    if(isIssuingH2DReq1) {
        H2DReq1[H2DReq1Counter] = H2DReqToIssue1;
        H2DReq1Counter++;
        isIssuingH2DReq1 = 0;
    }
    if(isIssuingH2DReq2) {
        printf("h2dreq is put into channel\n");
        H2DReq2[H2DReq2Counter] = H2DReqToIssue2;
        H2DReq2Counter++;
        isIssuingH2DReq2 = 0;
    }
    if(isIssuingH2DResp1) {
        // printf("H2D Resp was put into channel \n");
        H2DResp1[H2DResp1Counter] = H2DRespToIssue1;
        H2DResp1Counter++;
        isIssuingH2DResp1 = 0;
    }
    if(isIssuingH2DResp2) {
        
        H2DResp2[H2DResp1Counter] = H2DRespToIssue2;
        H2DResp2Counter++;
        isIssuingH2DResp2 = 0;
    }
        
    //d2h channels    
    if(isIssuingD2HData1) {
        D2HData1[D2HData1Counter] = D2HDataToIssue1;
        D2HData1Counter++;
        isIssuingD2HData1 = 0;
    }
    if(isIssuingD2HData2) {
        D2HData2[D2HData2Counter] = D2HDataToIssue2;
        D2HData2Counter++;
        isIssuingD2HData2 = 0;
    }
    if(isIssuingD2HReq1) {
        D2HReq1[D2HReq1Counter] = D2HReqToIssue1;
        D2HReq1Counter++;
        isIssuingD2HReq1 = 0;
    }
    if(isIssuingD2HReq2) {
        D2HReq2[D2HReq2Counter] = D2HReqToIssue2;
        D2HReq2Counter++;
        isIssuingD2HReq2 = 0;
    }
    if(isIssuingD2HResp1) {
        D2HResp1[D2HResp1Counter] = D2HRespToIssue1;
        D2HResp1Counter++;
        isIssuingD2HResp1 = 0;
    }
    if(isIssuingD2HResp2) {
        printf("d2h response issued from device 2\n");
        D2HResp2[D2HResp1Counter] = D2HRespToIssue2;
        D2HResp2Counter++;
        isIssuingD2HResp2 = 0;
    }
}



void type1_device_simulate(Cluster * cluster1, Cluster * cluster2, HA * home) {
    printf("%d %d\n", globalCounter, cluster1->cycle);

    while(globalCounter < 20) {
        int done[2] = {0, 0};
        for(int i = 1; i <= 2; i++) {
            unsigned id = nondet();
            id = id % 2;
            NONPROD_ASSERT(0 <= id && id <= 1, "unsigned integer after remainder of 2 should be between 0 and 1");
            //NONPROD_ASSERT(!done[id]);
            if(done[id])
                id = (id + 1) % 2;
            NONPROD_ASSERT(!done[id], "unsigned int 0 or 1 after + 1 should become 1 or 0");
            // NONPROD_ASSERT(0, "SMOKE NONDET_CHECK");
        
            //printf("chosen core %d to execute\n", id + 1);
            if(id == 0){
                printf("1!!\n");
                cluster_acts(cluster1, 1);
            }
            else{
                printf("2!!\n");
                cluster_acts(cluster2, 2);
            }
        
            done[id] = 1;
            //printf("%d %d\n", globalCounter, cluster1->cycle);

    
        }
        //printf("%d %d\n", globalCounter, cluster1->cycle);

        
        HA_acts();

        decide_HA_to_process_messages();

        update_cache_channels_messages();

        if(all_clusters_finished(cluster1, cluster2))
            break;
        globalCounter++;
        printf("%d %d\n", globalCounter, cluster1->cycle);
    }
}
void clear_H2DData(H2DData * h2dd) {
    h2dd->CQID = 0;
    h2dd->DataArrivedBeforeGO = 0;
    h2dd->payload[0] = 0;
    h2dd->payload[1] = 0;
    h2dd->requestorCluster = 0;
    h2dd->requestorCore = 0;
}
void clear_D2HData(D2HData * d2hd) {
    d2hd->UQID = 0;
    d2hd->payload[0] = 0;
    d2hd->payload[1] = 0;
    d2hd->requestorCluster = 0;
    d2hd->requestorCore = 0;
    d2hd->whichBlock = 0;
}
void clear_H2DReq(H2DRequest * h2dreq) {
    h2dreq->DataArrivedBeforeGO = 0;
    h2dreq->requestorCluster = 0;
    h2dreq->requestorCore = 0;
    h2dreq->type = 0;
    h2dreq->UQID = 0;
    h2dreq->whichBlock = 0;
}
void clear_D2HReq(D2HRequest * d2hreq) {
    d2hreq->DataArrivedBeforeGO = 0;
    d2hreq->requestorCluster = 0;
    d2hreq->requestorCore = 0;
    d2hreq->type = 0;
    d2hreq->CQID = 0;
    d2hreq->whichBlock = 0;
}
void clear_H2DResp(H2DResponse * h2dresp) {
    h2dresp->DataArrivedBeforeGO = 0;
    h2dresp->MESI_State = MESI_I;
    h2dresp->type = 4; //non of the defined
    h2dresp->requestorCluster = 0;
    h2dresp->requestorCore = 0;
    h2dresp->UQID = 0;
    h2dresp->whichBlock = 0;
}
void clear_D2HResp(D2HResponse * d2hresp) {
    d2hresp->DataArrivedBeforeGO = 0;
    d2hresp->type = 4; //non of the defined
    d2hresp->requestorCluster = 0;
    d2hresp->requestorCore = 0;
    d2hresp->CQID = 0;
    d2hresp->whichBlock = 0;
}
void initialise_channels() {
    H2DData1Counter = 0;
    H2DData2Counter = 0;
    for(int i = 0; i < MAX_MESSAGES_CHANNEL; i++) {
        clear_H2DData(&H2DData1[i]);
        clear_H2DData(&H2DData1[i]);
    }
    isIssuingH2DData1 = 0;
    isIssuingH2DData2 = 0;
    prevH2DDataBusy1 = 0;
    prevH2DDataBusy2 = 0;
    prevH2DDataBlocked1 = 0;
    prevH2DDataBlocked2 = 0;
    clear_H2DData(&H2DDataToIssue1);
    clear_H2DData(&H2DDataToIssue2);
    clear_H2DData(&H2DDataToProcess1);
    clear_H2DData(&H2DDataToProcess2);

    H2DReq1Counter = 0;
    H2DReq2Counter = 0;
    for(int i = 0; i < MAX_MESSAGES_CHANNEL; i++) {
        clear_H2DReq(&H2DReq1[i]);
        clear_H2DReq(&H2DReq2[i]);
    }
    isIssuingH2DReq1 = 0;
    isIssuingH2DReq2 = 0;
    prevH2DReqBusy1 = 0;
    prevH2DReqBusy2 = 0;
    prevH2DReqBlocked1 = 0;
    prevH2DReqBlocked2 = 0;
    clear_H2DReq(&H2DReqToIssue1);
    clear_H2DReq(&H2DReqToIssue2);
    clear_H2DReq(&H2DReqToProcess1);
    clear_H2DReq(&H2DReqToProcess2);
    
    H2DResp1Counter = 0;
    H2DResp2Counter = 0;
    for(int i = 0; i < MAX_MESSAGES_CHANNEL; i++) {
        clear_H2DResp(&H2DResp1[i]);
        clear_H2DResp(&H2DResp2[i]);
    }
    isIssuingH2DResp1 = 0;
    isIssuingH2DResp2 = 0;
    prevH2DRespBusy1 = 0;
    prevH2DRespBusy2 = 0;
    clear_H2DResp(&H2DRespToIssue1);
    clear_H2DResp(&H2DRespToIssue2);
    clear_H2DResp(&H2DRespToProcess1);
    clear_H2DResp(&H2DRespToProcess2);









    D2HData1Counter = 0;
    D2HData2Counter = 0;
    for(int i = 0; i < MAX_MESSAGES_CHANNEL; i++) {
        clear_D2HData(&D2HData1[i]);
        clear_D2HData(&D2HData1[i]);
    }
    isIssuingD2HData1 = 0;
    isIssuingD2HData2 = 0;
    prevD2HDataBusy1 = 0;
    prevD2HDataBusy2 = 0;
    clear_D2HData(&D2HDataToIssue1);
    clear_D2HData(&D2HDataToIssue2);
    clear_D2HData(&D2HDataToProcess1);
    clear_D2HData(&D2HDataToProcess2);

    D2HReq1Counter = 0;
    D2HReq2Counter = 0;
    for(int i = 0; i < MAX_MESSAGES_CHANNEL; i++) {
        clear_D2HReq(&D2HReq1[i]);
        clear_D2HReq(&D2HReq2[i]);
    }
    isIssuingD2HReq1 = 0;
    isIssuingD2HReq2 = 0;
    prevD2HReqBusy1 = 0;
    prevD2HReqBusy2 = 0;
    clear_D2HReq(&D2HReqToIssue1);
    clear_D2HReq(&D2HReqToIssue2);
    clear_D2HReq(&D2HReqToProcess1);
    clear_D2HReq(&D2HReqToProcess2);
    
    D2HResp1Counter = 0;
    D2HResp2Counter = 0;
    for(int i = 0; i < MAX_MESSAGES_CHANNEL; i++) {
        clear_D2HResp(&D2HResp1[i]);
        clear_D2HResp(&D2HResp2[i]);
    }
    isIssuingD2HResp1 = 0;
    isIssuingD2HResp2 = 0;
    prevD2HRespBusy1 = 0;
    prevD2HRespBusy2 = 0;
    clear_D2HResp(&D2HRespToIssue1);
    clear_D2HResp(&D2HRespToIssue2);
    clear_D2HResp(&D2HRespToProcess1);
    clear_D2HResp(&D2HRespToProcess2);



}
void initialise_HA() {
    for(int i = 0; i < MAX_BLOCKS_HA; i++){
        Host.dataBlocks[i][0] = 0; //block always filled with data 0 in byte 0, and 42 in byte 1
        Host.dataBlocks[i][1] = 42;

        Host.existsValidCopy[i] = 0;
        Host.stateBitVector[i][0] = 0; //is not owned by any peer caches
        //does not exist in any peer caches
        Host.stateBitVector[i][1] = 0;
        Host.stateBitVector[i][2] = 0;
    }
    
}

//TODO: haaving random evictions (over approximate replacement policy)

void type1_test1() {
    Cluster * cluster1 = (Cluster *) malloc(sizeof(Cluster));
    Cluster * cluster2 = (Cluster *) malloc(sizeof(Cluster));

    //initialise clusters and host,
    initialise_cluster(cluster1);
    cluster1->clusterId = 1;
    initialise_cluster(cluster2);
    cluster1->clusterId = 2;
    initialise_HA();
    //initialise CXL.cache channels
    initialise_channels();

    init_DCOH();
    
    
    //store x (HA) 1 + load y r1: executed by cluster 1's core 1 
    Instruction * write_X_1 = create_instruction(1, Write, 0, 1, 0);//write X 1
    // Instruction * read_Y_r1 = create_instruction(1, Read, 1, 0, 1); //read Y r1
    
    //load instructions into the program memory of clusters
    fill_program(cluster1, write_X_1, 1);
    // fill_program(cluster1, read_Y_r1, 1);
    // //store y (HA) 1 + load x r0: executed by cluster 2's core 2
    // Instruction * write_Y_1 = create_instruction(1, Write, 1, 1, 0);//write Y 1
    // Instruction * read_X_r0 = create_instruction(1, Read, 0, 0, 0); //read X r0
    // fill_program(cluster2, write_Y_1, 2);
    // fill_program(cluster2, read_X_r0, 2);

    //start running system with clusters and host
    type1_device_simulate(cluster1, cluster2, &Host);
    
    IMPORTANT_ASSERT(cluster1->cache1.externalBlocks[0][0] == 1, "cache 1 of cluster 1 got block X of HA");
    IMPORTANT_ASSERT(cluster1->cache1.externalBlocks[0][1] == 42, "should have received data from HA");

}

void type1_test2() {
    Cluster * cluster1 = (Cluster *) malloc(sizeof(Cluster));
    Cluster * cluster2 = (Cluster *) malloc(sizeof(Cluster));

    //initialise clusters and host,
    initialise_cluster(cluster1);
    cluster1->clusterId = 1;
    initialise_cluster(cluster2);
    cluster2->clusterId = 2;
    initialise_HA();
    //initialise CXL.cache channels
    initialise_channels();

    init_DCOH();

    cluster2->cache2.externalStates[1] = Modified;
    cluster2->cache2.externalBlocks[1][0] = 43;
    cluster2->cache2.externalBlocks[1][1] = 84;
    
    Host.existsValidCopy[1] = 1; //block 1 has a valid copy (in clustser 2)
    Host.stateBitVector[1][2] = MESI_M; //cluster 2 has block 1 in M state
    Host.stateBitVector[1][0] = 2; //owner is cluster 2

    DCOH2[1] = MESI_M;
    
    //Host.dataBlocks[1][1] 
    
    //store x (HA) 1 + load y r1: executed by cluster 1's core 1 
    Instruction * write_Y_1 = create_instruction(1, Write, 1, 1, 0);//write Y 1
    // Instruction * read_Y_r1 = create_instruction(1, Read, 1, 0, 1); //read Y r1
    
    //load instructions into the program memory of clusters
    fill_program(cluster1, write_Y_1, 1);//load instruction into core 1's program memory
    // fill_program(cluster1, read_Y_r1, 1);
    // //store y (HA) 1 + load x r0: executed by cluster 2's core 2
    // Instruction * write_Y_1 = create_instruction(1, Write, 1, 1, 0);//write Y 1
    // Instruction * read_X_r0 = create_instruction(1, Read, 0, 0, 0); //read X r0
    // fill_program(cluster2, write_Y_1, 2);
    // fill_program(cluster2, read_X_r0, 2);

    //start running system with clusters and host
    type1_device_simulate(cluster1, cluster2, &Host);
    
    IMPORTANT_ASSERT(cluster1->cache1.externalBlocks[1][0] == 1, "modified byte 0 of block Y on cache 1 of cluster 1");
    IMPORTANT_ASSERT(cluster1->cache1.externalBlocks[1][1] == 84, "cache 1 of cluster 1 got block Y of HA");

}