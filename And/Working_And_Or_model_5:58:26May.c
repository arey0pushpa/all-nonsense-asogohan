#include <stdio.h>
#include <stdlib.h>


#define M 6     
#define N 3
#define snareLength 6
#define len 5

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[snareLength] snareVector; 

unsigned int  nondet (){  
  unsigned int num = nondet_uint();
  __CPROVER_assume( num>= 0 && num  <= 1);
   return num;
};

unsigned int zeroTon(unsigned int n) {
    unsigned int result = nondet_uint();
    __CPROVER_assume(result >=0 && result <=n);
    return result ;
};

struct EdgeBag
 {
   unsigned int ith;
   unsigned int jth;
   unsigned int count;
   bitvector edgeWeight;
   snareVector zebra[snareLength];
   snareVector  vSnare;
   snareVector tSnare;
   snareVector combinedMask; 
};

// ------------------------------------------------ TESTED ---------------------------------------------------------

int  main()
 
 {    

    unsigned int pos, i, j, k, l, w, x, y , iVal, jVal, g, g0, gl, lastg, ng, nl, nl2 ;
    unsigned int edgePos = 0, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp, result;
    unsigned int  ticks, valj, vali , calc;
    unsigned int connectedArray[N] = {}, edgeCount = 0;
    _Bool Ck=0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5, C6 , C7; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, vl, vl2, t, f, v2, lastv, lastv2 ,nv, nv2, v0, v02 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N] , fComp , bComp;    
    snareVector friendMatrix[snareLength];     
    snareVector onOffMatrix[N], stCorres;
  
    unsigned int graph[N][N]; 




    //  Define the Container as Basis of our work  --------------------------
     struct EdgeBag edgeBag[len];
     //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
     edgePos = 0;
     for  (i = 0; i < N; i++) {
             for  (j = 0; j < N; j++) {
               if ((graph[i][j] == 1) || (graph[i][j] == 2)) {
                   edgeBag[edgePos].ith = i;     // Record the source node
                   edgeBag[edgePos].jth = j;     // Record the target Node
 
                   // Only molecule present at the nodes are allowed to fly out.
                   __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                   __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0); ;
 
                   // Additional Vedge[i][j] and Tedge[i][j] is used to be lookup value in global steady state check condition.
                   Vedge[i][j] = edgeBag[edgePos].vSnare;
                   Tedge[i][j] = edgeBag[edgePos].tSnare;
                   edgePos = edgePos + 1;
             }
 
             if ((graph[i][j] == 2)) {
                  edgeBag[edgePos].ith = i;      // Record the Source Node  
                  edgeBag[edgePos].jth = j;      // Record the Target Node
 
                 // Only molecule present at the nodes are allowed to fly out.
                   __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                   __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0);
                    // Additional Vedge2[i][j] and Tedge2[i][j] is used to be lookup value in global steady state check condition.
                   Vedge2[i][j] = edgeBag[edgePos].vSnare;
                   Tedge2[i][j] = edgeBag[edgePos].tSnare;
                   edgePos = edgePos + 1;
             }

          }
     }
     
// the code s for the new Insert usaga of the mandayams rewuest to make the model scalable upto lets sy surely N  = 10.
/*
 *Basic idea is to iterate over all graph cuts and then able to use the fact of the mengers theorem and the strongly connectivity of the graph
 *
 */
     for ( i = 0; i < len; i++) {

         for ( j = 0 ; j < len; j++) 

         {
                 // encode the logic and use the fact that hoe to use the theorems to take advantage of the fact that 
                 // mengers theorem works in this regards
         }
     }

    
     
     
     for  (i = 0; i < len; i++) {
        centTotal = 0b0;
        total = 0b0;
        ticks = 0;
		Ck = 0;
        
        //  Check if jth vSnare is present then check if all its t-snare frds are present on the edge. 
        //  If yes don't consider him as a cnadidate to check the fusion that happens btw current nodes.

        for  (j = 0; j < snareLength; j++) {
           v = edgeBag[i].vSnare;
           t = edgeBag[i].tSnare;
           f = friendMatrix[j];
           valj = edgeBag[i].jth;
           vali = edgeBag[i].ith;
          
           if( (v & (1 << j)) && ((t & f) != f) ){
              edgeBag[i].zebra[ticks] = f;
              centTotal = centTotal | f;
              ticks = ticks + 1;     
              if ( (((Tnodes[valj] & onOffMatrix[valj]) & f)  == f)  &&  ((onOffMatrix[vali] & f) != f)) {
                 Ck = Ck || 1 ;                                  
              }
           }
         }
           
         edgeBag[i].combinedMask = centTotal;
         edgeBag[i].count = ticks;

         if(Ck == 1) {
             C2 = C2 && 1;
         }
         else {
             C2 = C2 && 0;
         }

        for (k = 0; k < N; k++) {
			if( k != edgeBag[i].jth) {
				for ( l = 0; l < edgeBag[i].count ; l++) {
				    if (((onOffMatrix[k] & Tnodes[k]) & edgeBag[i].zebra[l]) != f){
					   C3 = C3 && 1;
				    }
				    else {
				       C3 = 0;
				   }
		        }
		    }
		} 

    }

    
//  BASIC BLOCK ENDS -----------------------------------------------------------------------------------------
   
    for  (i = 0; i < len; i++) {

        printf("The edge No.%d has this config : \n There is an edge between graph[%d][%d]" , i , edgeBag[i].ith, edgeBag[i].jth);

        printf (" vSnare =  %d \n tSnare = %d\n combinedMask = %d \n counts = %d " ,edgeBag[i].vSnare , edgeBag[i].tSnare, edgeBag[i].combinedMask, edgeBag[i].count);
   
   }


    printf("\nThe value of : \n C0 = %d \n C1 : %d \n C2 : %d , C3 : %d \n,C4 : %d , C5 : %d",C0,C1,C2,C3,C4,C5);
    printf(" the value of mr.Ticks is %d and len was %d ", ticks , len);
    
  // assert(0);
  __CPROVER_assert(!(C0 && C1 && C2 && C3 && C4 && C5) , "Graph that satisfy friendZoned model exists");  
 
}

