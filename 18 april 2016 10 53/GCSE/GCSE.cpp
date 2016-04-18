#define DEBUG_TYPE "csepass"
#define MAXBB 1024
#include "includefiles.h"
#include <limits>
using namespace std;
using namespace llvm;


int blockCount=0;
int functionCount=0;
unsigned long long int exprsnNo=1;
unsigned long long int LatticeSize;
//sets
struct operand_list
{
	set<string> operands;
};

set<string> ExpSet;

//hash maps
std::map<string,unsigned long long int> InsValMap;
std::map<unsigned long long int,string>InsValStrMap;
std::map<unsigned long long int,Instruction*>InsValInsMap;
std::map<unsigned long long int,string>InsValVarMap ;
int nextInsValue=1;
int INF=999999999;

long long int transferFunction(Function::iterator inputBB, unsigned long long int latticePoint);

string instructionToString(Instruction* curr_Ins)
{
	Instruction *InsOp1, *InsOp2;
	Value *v;
	string op1="'",op2="'",exprsn,opcodeName,opc;
	LoadInst *LD;
	InsOp1 = cast<Instruction>(curr_Ins->getOperand(0));
	InsOp2 = cast<Instruction>(curr_Ins->getOperand(1));
	opcodeName=InsOp1->getOpcodeName();
	if(opcodeName=="load")
	{
		LD = cast<LoadInst>(curr_Ins->getOperand(0));
		v=LD->getOperand(0);
		op1=v->getName().str();
	}
	else
	{	
		op1=instructionToString(InsOp1);
	}
	opcodeName=InsOp2->getOpcodeName();
	if(opcodeName=="load")
	{
		LD = cast<LoadInst>(curr_Ins->getOperand(1));
		v=LD->getOperand(0);
		op2=v->getName().str();
	}
	else
	{
		op2=instructionToString(InsOp2);
	}
	switch(curr_Ins->getOpcode()){ 
							case Instruction::Add: opc="+";
													break;
							case Instruction::Sub: opc="-";
													break;
							case 21:			   opc="/";
													break;
							case Instruction::Mul: opc="*";
													break;}
	exprsn=op1+opc+op2;
	return exprsn;
}

/******************Floyd Warshal Algorithm****************************************************/
/*Refernce : http://www.geeksforgeeks.org/dynamic-programming-set-16-floyd-warshall-algorithm/
**********************************************************************************************/

void floydWarshell(int **graph,int **dist,int ch)
{
    /* dist[][] will be the output matrix that will finally have the shortest 
      distances between every pair of vertices */
    int i, j, k;
 
    /* Initialize the solution matrix same as input graph matrix. Or 
       we can say the initial values of shortest distances are based
       on shortest paths considering no intermediate vertex. */
    for (i = 0; i < ch; i++)
        for (j = 0; j < ch; j++)
            dist[i][j] = graph[i][j];
 
    /* Add all vertices one by one to the set of intermediate vertices.
      ---> Before start of a iteration, we have shortest distances between all
      pairs of vertices such that the shortest distances consider only the
      vertices in set {0, 1, 2, .. k-1} as intermediate vertices.
      ----> After the end of a iteration, vertex no. k is added to the set of
      intermediate vertices and the set becomes {0, 1, 2, .. k} */
    for (k = 0; k < ch; k++)
    {
        // Pick all vertices as source one by one
        for (i = 0; i < ch; i++)
        {
            // Pick all vertices as destination for the
            // above picked source
            for (j = 0; j < ch; j++)
            {
                // If vertex k is on the shortest path from
                // i to j, then update the value of dist[i][j]
                if (dist[i][k] + dist[k][j] < dist[i][j])
                    dist[i][j] = dist[i][k] + dist[k][j];
            }
        }
    }
 
}


void runOnEachInstructions(BasicBlock::iterator i)
{
	string curr_Ins_Str;
	Instruction* curr_Ins;
	curr_Ins = cast<Instruction>(i);
	string varName;
	switch(curr_Ins->getOpcode()){ //each function invocation below returns EOUT in current iteration..        
							case Instruction::Add: 
							case Instruction::Sub:
							case 21:
							case Instruction::Mul: {
								curr_Ins_Str= instructionToString(curr_Ins);
								if(ExpSet.find(curr_Ins_Str) == ExpSet.end()) {
										ExpSet.insert(curr_Ins_Str);
										InsValMap[curr_Ins_Str]=exprsnNo;
										InsValStrMap[exprsnNo]=curr_Ins_Str;
										InsValInsMap[exprsnNo]=curr_Ins;
										varName="temp"+itoa(exprsnNo);
										InsValVarMap[exprsnNo]=varName;
										errs()<<"\n"<<"Expression Found \n"<<exprsnNo<<" "<<curr_Ins_Str;
										exprsnNo*=2;			 
							}

		}
	
}
}

void runOnEachBlocks(Function::iterator b)
 {
	 blockCount++;
	 for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie;++i){
		 runOnEachInstructions(i);
	}
}
 
 
int runOnEachFunctions(Function &F)
{
	functionCount++;
	if(functionCount>1)
			return -1;
	for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
				{
					errs()<<"\n"<<b->getName()<<"\n";
					runOnEachBlocks(b);
				}
	}
	Function::iterator tempBB=F.begin();
	LatticeSize=exprsnNo;
	//errs()<<"\nLatticeSize="<<LatticeSize;
	//Function::iterator b = F.begin();
	//errs()<<"Result = "<<transferFunction(b,0);
	/****************************************
	***  creating the control flow graph  ***
	****************************************/
	
	errs()<<"\nBasic block = "<<blockCount<<"\n";
	Function::iterator temp2 = F.begin();
	Function::iterator basicBlockList[blockCount];
	BasicBlock* tempbb = dyn_cast<BasicBlock>(&*temp2);
	succ_iterator successor_begin_array[MAXBB]=succ_begin(tempbb);
	succ_iterator successor_end_array[MAXBB]=succ_begin(tempbb);

		/**************************************
		*** Finding Succ and pred of each   ***
		*** basic blocks                    ***
		**************************************/
	
	int bblockno=0;
	for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) //no of blocks CFG succ gen
	{
		basicBlockList[bblockno]=b;
		BasicBlock* bb = dyn_cast<BasicBlock>(&*b);
		successor_begin_array[bblockno] = succ_begin(bb);
		successor_end_array[bblockno] = succ_end(bb);
		bblockno++;
	}
	/*int** ary = new int*[rowCount];
	for(int i = 0; i < rowCount; ++i)
    	ary[i] = new int[colCount];*/


		/**************************************
		*** Initialize Control flow graph   ***
		**************************************/		
    
    int cfg_graph_visited[blockCount];
	int cfg_rep[blockCount][blockCount];
	for(int fori=0;fori<blockCount;fori++)
	{
		cfg_graph_visited[fori]=0; 
		for(int forj=0;forj<blockCount;forj++)
			cfg_rep[fori][forj]=0;
	}



	int index1=0;
	while(index1<blockCount)
	{
		cfg_graph_visited[index1]=1;
		loopy:
		if(successor_begin_array[index1]==successor_end_array[index1])
	    {
		   index1++;
		   continue;
	    }
		else
		{
		    BasicBlock *TheSucc = *successor_begin_array[index1];
			for(int index2=0; index2<blockCount;index2++)
			{
			    BasicBlock* bb = dyn_cast<BasicBlock>(&*basicBlockList[index2]);
				if(TheSucc == bb)
				cfg_rep[index1][index2]=1;
			}
			++successor_begin_array[index1];
			goto loopy;
		}
		index1++;					    
	}
	for(int index1=0;index1<blockCount;index1++)
	{
		errs()<<"\n"<<index1<<" "<<basicBlockList[index1]->getName()<<"\n";
	}

	

		/**************************************
		*** Printing the Control Flow       ***
		**************************************/

	errs()<<"\n CFG \n";
	for(int index1=0;index1<blockCount;index1++)
	{
		for(int index2=0;index2<blockCount;index2++)
		   errs()<<cfg_rep[index1][index2]<<" ";
		errs()<<"\n";
	}

	unsigned long long int ch = (LatticeSize)*2*blockCount;
	errs()<<"\nValue of ch = "<<ch<<"\n";
	int **final_graph;
	int **dist; 
	final_graph = new int*[ch]; 
	dist = new int*[ch];
	for (int i = 0; i < ch; i++){
    	final_graph[i] = new int[ch];
    	dist[i]=new int[ch];
	}
	for(long long int fori=0;fori<ch;fori++)
		for(long long int forj=0;forj<ch;forj++)
			{
				if(fori!=forj) final_graph[fori][forj]=INF;
				else final_graph[fori][forj]=0;
			}
	for(int bbNum=0;bbNum<blockCount;bbNum++)
	{
		for(unsigned long long int latticeNum=0;latticeNum<LatticeSize;latticeNum++)
		{
			errs()<<"\nBBNUM "<<bbNum<<" lattice "<<latticeNum;
			unsigned long long int result=transferFunction(basicBlockList[bbNum],latticeNum);
			errs()<<" result "<<result;
			unsigned long long int start=(bbNum*2*LatticeSize)+latticeNum;
			unsigned long long int end=(bbNum*2*LatticeSize)+LatticeSize+result;
							//if(start==8 && end==12) errs()<<" bb no "<<bbNum<<" "<<latticeNum<<" "<<result<<" "<<start<<" "<<end;
			final_graph[start][end]=1;
		}
		for(int rbbNum=0;rbbNum<blockCount;rbbNum++)
		{
			if(cfg_rep[bbNum][rbbNum]==1)
			{
				for(int latticeNum=0;latticeNum<LatticeSize;latticeNum++)
				{
					unsigned long long int start=(bbNum*2*LatticeSize)+LatticeSize+latticeNum;
					unsigned long long int end=(rbbNum*2*LatticeSize)+latticeNum;
					final_graph[start][end]=1;
				}
			}
		}
	}
	/************* printing matrix to file *****************/
	/*
		PPPPPPPPPPPPP
	errs()<<ch;
	ofstream myfile;
  	myfile.open ("example.txt");
	errs()<<"\n\n\n";
	for(long long int fori=0;fori<ch;fori++){
		for(long long int forj=0;forj<ch;forj++)
			{
				if(final_graph[fori][forj]>10) myfile<<0<<" "; else
				myfile<<final_graph[fori][forj]<<" ";
			}
			myfile<<"\n";
	}
	myfile.close();
	/************* printing matrix to file *****************/

	floydWarshell(final_graph,dist,ch);
	unsigned long long int out[blockCount];
	for(int bbNum=0;bbNum<blockCount;bbNum++)
	{
		unsigned long long int res=0;
		for(unsigned long long int latticeNum=0;latticeNum<LatticeSize;latticeNum++)
						{
							unsigned long long int start=LatticeSize+(2*bbNum*LatticeSize)+latticeNum;
							if(dist[0][start]<INF)
							{
								//errs()<<"\nOK "<<bbNum<<" start="<<start<<" latt="<<latticeNum;
								if(res==0)
									res=latticeNum;
								else
									res=res & latticeNum;
							}
						}
						errs()<<"\n\n"<<bbNum<<" "<<basicBlockList[bbNum]->getName()<<"\n";
						errs()<<" res = "<<res;
						out[bbNum]=res;
	}
	unsigned long long int in[blockCount];
	unsigned long long int zero=0;
	errs()<<"Available Expressions Per Block";
	for(int bbNum=0;bbNum<blockCount;bbNum++)
	{
		in[bbNum]=0;
		for(int bbNum2=0;bbNum2<blockCount;bbNum2++)
		{
			if(cfg_rep[bbNum2][bbNum]==1)
			{
				if(in[bbNum]==0)
					in[bbNum]=out[bbNum2];
				else
					in[bbNum] = in[bbNum] & out[bbNum2];
			}
		}
		errs()<<"\n\n"<<bbNum<<" "<<basicBlockList[bbNum]->getName()<<" "<<in[bbNum];
	}

	
	
	return 0;
}

string getOperandName(BasicBlock::iterator inst)
{
	return (inst->getOperand(1))->getName().str();
}

long long int transferFunction(Function::iterator inputBB, unsigned long long int latticePoint)
{
	unsigned long long int wlatticePoint=latticePoint;
	unsigned long long int wexprsnNo=exprsnNo;
	string exprsn2;
	Instruction* curr_Ins;
	for (BasicBlock::iterator i = inputBB->begin(), ie = inputBB->end(); i != ie;++i){
		curr_Ins = cast<Instruction>(i);
		switch(curr_Ins->getOpcode()){
			case Instruction::Store:{
				string opname_to_delt = getOperandName(i);
				//errs()<<"\nopname to delete"<<opname_to_delt<<"\n";
				unsigned long long int latticeContents = pow(2,floor(log2(wlatticePoint)));
				//errs()<<"\nStore operation ";curr_Ins->print(errs());
				while(latticeContents>=1)
				{
					if(wlatticePoint & latticeContents)
						{
							//errs()<<"Deleteion Here";
							string expression=InsValStrMap[latticeContents];
							size_t position=expression.find(opname_to_delt); //checking for variable name in expression has to double check.
							bool flagTemp=1;
							if(position<string::npos)
							{
									if(position+opname_to_delt.length()==expression.length())
									{

									}
									else
									{
										switch(expression[position+opname_to_delt.length()])
										{
											case '+':
											case '-':
											case '/':
											case '*':
													break;
											default:flagTemp=0;
													//errs()<<"\n\nDefault : "<<expression<<" "<<opname_to_delt<<" "<<expression[position+opname_to_delt.length()];
										}
									}
									if(position==0&&flagTemp)
									{

									}
									else if(flagTemp)
									{
										switch(expression[position-1])
										{
											case '+':
											case '-':
											case '/':
											case '*':
													break;
											default:flagTemp=0;
													//errs()<<"\n\nDefault2 : "<<expression<<" "<<opname_to_delt<<" "<<expression[position+opname_to_delt.length()];
										}
									}
								if(flagTemp) //delete expression from the lattice point
									{
										wlatticePoint = (wlatticePoint & (~latticeContents));
										//errs()<<"\nDelete Exp "<<expression<<" op "<<opname_to_delt<<" "<<position;
									}
							}
						}
						else
						{
							//errs()<<"Deletion not";
						}
					latticeContents/=2;
				}
				break;
			}
				
			
			case Instruction::Add: 
			case Instruction::Sub:
			case 21:
			case Instruction::Mul:{
				//errs()<<"Instruction -> ";
					//curr_Ins->print(errs());
					//break;
					exprsn2=instructionToString(curr_Ins);
					//errs()<<"\nAdd Expression "<<exprsn2<<" "<<InsValMap[exprsn2];
					wlatticePoint = wlatticePoint | InsValMap[exprsn2];
					//errs()<<" lattice now = "<<wlatticePoint;
					break;
	}
	default: break;
}
}

	
	return wlatticePoint;
}








namespace {
	struct GCSE : public FunctionPass {
		static char ID; // Pass identification, replacement for typeid
		
		GCSE() : FunctionPass(ID) { 
						
						}
     	
		~GCSE() {		
					}
		virtual bool runOnFunction(Function &F) {
				
				
				if(runOnEachFunctions(F)<0) errs()<<"There should not be more than one function";
				//unsigned long long int check = std::numeric_limits<unsigned long long int>::max();			
				//check = (unsigned long long int)log2(check);
				//errs()<<check;
				//errs()<<"\n"<<check/8;
				

		return false;
		}
	};
}

char GCSE::ID = 0;
static RegisterPass<GCSE> X("GCSE", "Print Instructions");



