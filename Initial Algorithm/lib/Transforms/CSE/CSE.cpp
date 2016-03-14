#define DEBUG_TYPE "csepass"
#define SIZE 1024
#include <includefiles.h>
#include <tgmath.h>

using namespace std;
using namespace llvm;

Instruction* curr_Ins,*dup_Ins,*ins_del,*temp_Ins,*str_del;
struct struct_instruction
{
Instruction *inst;
long int value;
struct struct_instruction * next;
};
struct instruction_set
{
	Instruction *inst;
	long int value;
};


struct struct_instruction *head=NULL; 
long int ks_value=0;
std::map<long int, BasicBlock*> BBMap;
std::map<string,Instruction*> InsMap;
std::map<string,long int> InsValueMap;
std::map<long int,string>InsValueStingMap;
std::map<long int,Instruction*> InsInstrMap;
std::map<string, set<string> > AvaiExp;
std::map<string, set<string> > VarExp;
set<string> ExpSet;
std::map<Value*,int> Opr;
int itr=0;
LoadInst *LD;
Value *v;
string opcode,opr1,opr2,exprsn,testOp;
int INF=32222;

int dist[SIZE][SIZE];



void printInstructions(long int input)
{
	long int tempinput=input;
	int instructioncount=(int)log2(input)+1;
	while(instructioncount-->=0)
	{
		if(input-(pow(2,instructioncount))>=0)
		{
			errs()<<InsValueStingMap[pow(2,instructioncount)]<<" ";
			input-=(pow(2,instructioncount));
		}
	}
}


void floydWarshell(int graph[][SIZE],int ch)
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







int transferFunction(Function::iterator inputBB,long int input)
{
	long int inputbu=input;
	list<struct instruction_set> ins_set;
	set<string> BlockSet;
	int ks_pvalue=ks_value;
	bool tobinary[ks_value+1];
	for(int fori=0;fori<=ks_value;fori++) tobinary[fori]=0;
	int tempinput=input;
	int tempindex=0;
	int noofones=0;
	long int gen=0;
	/*Segment 1*/
	std::list<struct instruction_set> locallist;
	for (BasicBlock::iterator i = inputBB->begin(), ie = inputBB->end(); i != ie;++i){
		
		curr_Ins = cast<Instruction>(i);
		switch(curr_Ins->getOpcode()){
			
			case Instruction::Store:{
				string opname_to_delt = (i->getOperand(1))->getName().str();
				//errs()<<"\nTo Delete = "<<opname_to_delt;
				struct struct_instruction *temp=head;
							while(temp!=NULL)  // printing the list of expressions
							{
							
							if(temp->inst->getOpcode()==Instruction::Add) opcode="+";
							LD = cast<LoadInst>(temp->inst->getOperand(0));
							v=LD->getOperand(0);
							opr1=v->getName().str();
							LD = cast<LoadInst>(temp->inst->getOperand(1));
							v=LD->getOperand(0);
							opr2=v->getName().str();
							exprsn=opr1+opcode+opr2;
							if(opr1==opname_to_delt||opr2==opname_to_delt)
							{input=(input & (~InsValueMap[exprsn]));
								//errs()<<"\n To delete = "<<InsValueMap[exprsn]<<" \n";
								}
							
							temp=temp->next; 
							 }
				/*Segment 2*/
				 break;
			}
			
			case Instruction::Add: 
			case Instruction::Sub:
			case 21:
			case Instruction::Mul:{
				if(curr_Ins->getOpcode()==Instruction::Add) opcode="+";
				else if(curr_Ins->getOpcode()==Instruction::Sub) opcode="-";
				else if(curr_Ins->getOpcode()==21) opcode="/";
				else if(curr_Ins->getOpcode()==Instruction::Mul) opcode="*";
				LD = cast<LoadInst>(curr_Ins->getOperand(0));
							v=LD->getOperand(0);
							opr1=v->getName().str();
							LD = cast<LoadInst>(curr_Ins->getOperand(1));
							v=LD->getOperand(0);
							opr2=v->getName().str();
							exprsn=opr1+opcode+opr2;
							if(BlockSet.find(exprsn) == BlockSet.end()) {
										BlockSet.insert(exprsn);
										//errs()<<"\nBasic Block 1 "<<exprsn<<"\n";
										struct instruction_set newnode_temp;
										newnode_temp.inst=curr_Ins;
										newnode_temp.value=InsValueMap[exprsn];
										locallist.push_back(newnode_temp);
										gen+=newnode_temp.value;
										input = input | newnode_temp.value;
												
							}
							else
							{
								//errs()<<"\nduplicate : "<<opr1<<opcode<<opr2;
							}
				
				break;
			}
		}
		
		
		
	}
	return input;
	
}






namespace {
	struct CSE : public FunctionPass {
		static char ID; // Pass identification, replacement for typeid
		
		CSE() : FunctionPass(ID) { 
						
						}
     	
		~CSE() {
						
					}
		virtual bool runOnFunction(Function &F) {
			int block_number=0;
			
			for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
				errs()<<"Basic Block "<<++block_number<<"\n";
				for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie;++i){
					
					curr_Ins = cast<Instruction>(i);
					switch(curr_Ins->getOpcode()){ //each function invocation below returns EOUT in current iteration..        
							case Instruction::Add: 
							case Instruction::Sub:
							case 21:
							case Instruction::Mul: { //errs()<<"Addition Found\n";
								//curr_Ins->print(errs());
								//errs()<<"\n";
								if(curr_Ins->getOpcode()==Instruction::Add) opcode="+";
								else if(curr_Ins->getOpcode()==Instruction::Sub) opcode="-";
								else if(curr_Ins->getOpcode()==21) opcode="/";
								else if(curr_Ins->getOpcode()==Instruction::Mul) opcode="*";
								LD = cast<LoadInst>(curr_Ins->getOperand(0));
								v=LD->getOperand(0);
								opr1=v->getName().str();
								LD = cast<LoadInst>(curr_Ins->getOperand(1));
								v=LD->getOperand(0);
								opr2=v->getName().str();
								exprsn=opr1+opcode+opr2;
								errs()<<"\n"<<exprsn<<"\n";
								if(ExpSet.find(exprsn) == ExpSet.end()) {
										ExpSet.insert(exprsn);
							             struct struct_instruction *node = new struct struct_instruction;
										 node->inst=curr_Ins;
										 node->value=pow(2,ks_value);
										 InsValueMap[exprsn]=node->value;
										 InsInstrMap[node->value]=curr_Ins;
										 InsValueStingMap[node->value]=exprsn;
										 node->next=NULL;
										 ks_value++;
										 struct struct_instruction * temp= head;
										 if(temp==NULL) head=node;
										 else
										 {
										 while(temp->next!=NULL) temp=temp->next;
										 temp->next=node;
										 } }
										 break;
										}
							
							default:{ 
												
							}}
							
						}
					
				}
			
			
			//traversal
							errs()<<"Output\n";
							struct struct_instruction *temp=head;
							while(temp!=NULL)  // printing the list of expressions
							{
							errs()<<temp->value<<"\t";
							temp->inst->print(errs());
							
							errs()<<"\n";
							opcode="+"; //name resolving
							LD = cast<LoadInst>(temp->inst->getOperand(0));
							v=LD->getOperand(0);
							opr1=v->getName().str();
							LD = cast<LoadInst>(temp->inst->getOperand(1));
							v=LD->getOperand(0);
							opr2=v->getName().str();
							exprsn=opr1+opcode+opr2;
							errs()<<"\n"<<exprsn<<"\n";
							 temp=temp->next; 
							 }
							
							Function::iterator basicBlockList[block_number];
							Function::iterator temp2 = F.begin();
							BasicBlock* tempbb = dyn_cast<BasicBlock>(&*temp2);
							
							succ_iterator successor_begin_array[100]=succ_begin(tempbb);
							succ_iterator successor_end_array[100]=succ_begin(tempbb);
							int bblockno=0;
							for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) //no of blocks CFG succ gen
						    {
								
								basicBlockList[bblockno]=b;
								BasicBlock* bb = dyn_cast<BasicBlock>(&*b);
								successor_begin_array[bblockno] = succ_begin(bb);
								successor_end_array[bblockno] = succ_end(bb);
								bblockno++;
								errs()<<bblockno<<"\n";
								
							}
						    
						    
						    int cfg_graph_visited[block_number];
						    int cfg_rep[block_number][block_number];
						    for(int fori=0;fori<block_number;fori++)
						         {
									 cfg_graph_visited[fori]=0; 
									 for(int forj=0;forj<block_number;forj++)
										cfg_rep[fori][forj]=0;
								}
						    int index1=0;
						    while(index1<block_number)
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
									   for(int index2=0; index2<block_number;index2++)
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
						     errs()<<"\n CFG \n";
						     for(int index1=0;index1<block_number;index1++)
								{
									for(int index2=0;index2<block_number;index2++)
									    errs()<<cfg_rep[index1][index2]<<" ";
									 errs()<<"\n";
							     }
					long long int ch = (pow(2,ks_value))*2*block_number;
					long long int latticeSize = (pow(2,ks_value));
					errs()<<" \n ch = "<<(int)(pow(2,ks_value)-1)<<" "<<block_number<<" "<<ch;
					int final_graph[ch][SIZE];
					for(long long int fori=0;fori<ch;fori++)
					for(long long int forj=0;forj<ch;forj++)
						{
							if(fori!=forj) final_graph[fori][forj]=INF;
							else final_graph[fori][forj]=0;
						}
					//errs()<<transferFunction(basicBlockList[0],0);
					errs()<<"\n bb "<<block_number;
				    for(int bbNum=0;bbNum<block_number;bbNum++)
				    {
						for(int latticeNum=0;latticeNum<latticeSize;latticeNum++)
						{
							int result=transferFunction(basicBlockList[bbNum],latticeNum);
							
							long long start=(bbNum*2*latticeSize)+latticeNum;
							long long end=(bbNum*2*latticeSize)+latticeSize+result;
							//if(start==8 && end==12) errs()<<" bb no "<<bbNum<<" "<<latticeNum<<" "<<result<<" "<<start<<" "<<end;
							final_graph[start][end]=1;
						}
						errs()<<"\n here \n";
						for(int rbbNum=0;rbbNum<block_number;rbbNum++)
						{
							if(cfg_rep[bbNum][rbbNum]==1)
							{
								for(int latticeNum=0;latticeNum<latticeSize;latticeNum++)
								{
									long long start=(bbNum*2*latticeSize)+latticeSize+latticeNum;
									long long end=(rbbNum*2*latticeSize)+latticeNum;
									if(start==8 && end==12) errs()<<"\n destination  "<<bbNum<<" "<<rbbNum<<" "<<latticeNum<<" "<<start<<" "<<end;
									final_graph[start][end]=1;
								}
							}
						}
					}
					errs()<<"\n\n\n\n\n";
					floydWarshell(final_graph,ch);
					/*for(int fori=0;fori<ch;fori++){
						for(int forj=0;forj<ch;forj++)
							errs()<<final_graph[fori][forj]<<" ";
						errs()<<"\n";}*/
					//errs()<<"\nBlock Number "<<block_number<<"\n";
					
					//for(int fori=0;fori<ch;fori++)
						//errs()<<fori<<" "<<dist[0][fori]<<"\n";
						//errs()<<"\nlattice size = "<<latticeSize;
					for(int bbNum=0;bbNum<block_number;bbNum++)
					{
						int res=0;
						for(int latticeNum=0;latticeNum<latticeSize;latticeNum++)
						{
							long long start=latticeSize+(2*bbNum*latticeSize)+latticeNum;
							if(dist[0][start]<INF)
							{
								//errs()<<"\nOK "<<bbNum<<" start="<<start<<" latt="<<latticeNum;
								if(res==0)
									res=latticeNum;
								else
									res=res & latticeNum;
							}
						}
						errs()<<"\nBlock Number "<<bbNum<<" res = "<<res;
						printInstructions(res);
					}
			//int result=transferFunction(basicBlockList[1],2);
			//printInstructions(result);		
							
					  		  				
		return false;
		}
	};
}

char CSE::ID = 0;
static RegisterPass<CSE> X("CSE", "Print Instructions");
