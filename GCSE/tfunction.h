int transferFunction(Function::iterator inputBB,int input)
{
	list<struct instruction_set> ins_set;
	set<string> BlockSet;
	int ks_pvalue=ks_value;
	bool tobinary[ks_value+1];
	for(int fori=0;fori<=ks_value;fori++) tobinary[fori]=0;
	int tempinput=input;
	int tempindex=0;
	int noofones=0;
	while(tempinput>0)
	{
		tobinary[tempindex++]=tempinput%2;
		if(tempinput%2==1) noofones++;
		tempinput/=2;
	}
	Instruction *inst_set[noofones];
	long int inst_set_value[noofones];
	int inst_set_ptr=0;
	for(int fori=0;fori<=ks_value;fori++) errs()<<tobinary[fori]<<" ";
	struct struct_instruction *temp=head;
	for(int fori=0;fori<=ks_value;fori++){
			if(temp!=NULL)
							{
							if(tobinary[fori]==1){
							inst_set[inst_set_ptr]=temp->inst;
							inst_set_value[inst_set_ptr++]=temp->value;
							}
							 temp=temp->next; }
		
	}
	errs()<<"\nChecking for stability\n";
	for(int fori=0;fori<noofones;fori++) { errs()<<"\n"; inst_set[fori]->print(errs());
		
		
		LD = cast<LoadInst>(inst_set[fori]->getOperand(0));
							v=LD->getOperand(0);
							opr1=v->getName().str();
							LD = cast<LoadInst>(inst_set[fori]->getOperand(1));
							v=LD->getOperand(0);
							opr2=v->getName().str();
							exprsn=opr1+opcode+opr2;
							errs()<<"\n"<<exprsn<<"\n";
		
		
		
		 } //input is ready upto here
	errs()<<"\nChecking for instruction;";
	std::list<struct instruction_set> locallist;
	for (BasicBlock::iterator i = inputBB->begin(), ie = inputBB->end(); i != ie;++i){
		
		curr_Ins = cast<Instruction>(i);
		//curr_Ins->print(errs());
		
		switch(curr_Ins->getOpcode()){
			
			case Instruction::Store: {
				string opname_to_delt = (i->getOperand(1))->getName().str();
				errs()<<"\nTo Delete = "<<opname_to_delt;
				for(int fori=0;fori<inst_set_ptr;fori++)
				 {
					 LD = cast<LoadInst>(inst_set[fori]->getOperand(0));
							v=LD->getOperand(0);
							opr1=v->getName().str();
							LD = cast<LoadInst>(inst_set[fori]->getOperand(1));
							v=LD->getOperand(0);
							opr2=v->getName().str();
					 if(opr1.compare(opname_to_delt)==0||opr2.compare(opname_to_delt)==0)
					  {
						 inst_set_value[fori]=0;
						 errs()<<"\n"<<opr1<<"+"<<opr2<<"\n";
					  }
				 }
				 std::list<struct instruction_set>::const_iterator iterator;
				for (iterator = locallist.begin(); iterator != locallist.end(); ++iterator) {
						errs()<<"\n"<<iterator->value<<" works here\n";
				}
				 break;
			}
			
			case Instruction::Add: {
				opcode="+";
				LD = cast<LoadInst>(curr_Ins->getOperand(0));
							v=LD->getOperand(0);
							opr1=v->getName().str();
							LD = cast<LoadInst>(curr_Ins->getOperand(1));
							v=LD->getOperand(0);
							opr2=v->getName().str();
							exprsn=opr1+opcode+opr2;
							if(BlockSet.find(exprsn) == BlockSet.end()) {
										BlockSet.insert(exprsn);
										errs()<<"\nBasic Block 1 "<<exprsn<<"\n";
										struct instruction_set newnode_temp;
										newnode_temp.inst=curr_Ins;
										newnode_temp.value=InsValueMap[exprsn];
										locallist.push_back(newnode_temp);
												
							}
							else
							{
								errs()<<"\nduplicate : "<<opr1<<opcode<<opr2;
							}
				
				break;
			}
		}
		
		
	}
}
