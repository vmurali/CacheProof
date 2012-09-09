Load Mesg.

Inductive Point := p | c.
Definition State := nat.

Module RespMesg <: Mesg.
  Definition mesg := (State * State)%type.
End RespMesg.