import {CubicalDeclarationTransaction} from "./cubical-transaction.mjs";

// One publication boundary is an ordinary declaration or a generated family.
// Prepare frontend records while the native checkpoint is open. Only publish
// them after checking and observers finish, so rollback needs no copies of
// previously published inspection maps. The translator owns environment values
// and family dependencies; identity reservations grant no availability.
export class CubicalPublication {
  constructor(program) {
    this.program=program;
    this.statements=[];
    this.records=[];
    this.start=null;
    this.group=false;
    this.transaction=null;
  }
  begin(group=false) {
    if(this.start!==null)throw new Error("A publication is already active.");
    this.start=this.statements.length;
    this.group=group;
    if(group||this.program.manageTransactions)
      this.transaction=new CubicalDeclarationTransaction(this.program.kernel,this.program.checker);
  }
  beginDeclaration() { if(!this.group)this.begin(); }
  endDeclaration(accept) {
    // Ordinary refusals retain partial proof statements for inspection, as
    // before. A refused generated family discards all its members together.
    if(!this.group)this.finish(accept,true);
  }
  finish(accept,keepStatements=false) {
    const {transaction,records,start}=this;
    this.transaction=null;this.records=[];this.start=null;this.group=false;
    if(!accept&&!keepStatements)this.statements.length=start;
    transaction?.finish(accept);
    if(accept)for(const record of records)this.program.publishReferences(record);
  }
  abort() { if(this.start!==null)this.finish(false); }
}
