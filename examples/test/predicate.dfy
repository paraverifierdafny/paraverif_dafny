class Test {

    var users : array<User>;
    var size : int;
    var index : int;

    method Init(c : int)
    modifies this;   
    requires c > 0;
    ensures fresh(users);   
    ensures size == c; 
    ensures Check();
    ensures Empty();
    {
        users := new User[c];   
        size := c;    
        index := -1;        
    }

predicate Empty()
reads this`index;
{
    index == -1
}

predicate Full()
reads this`index, this`size;
{
    index == (size - 1)
}

predicate Check()
reads this;
{
    users != null && 
    size > 0 && 
    size == users.Length && 
    index >= -1 && 
    index < size 
}

method AddUser(u : User)
modifies this.users, this`index;
requires Check();
requires !Full();

ensures Check();
ensures index == old(index) + 1;
ensures users[index] == u;
{
    index := index + 1;   
    users[index] := u; 
}

predicate FindUserById(n : int)
reads this.users, this.users`id;
requires Check();
{
    exists i :: 0 <= i < users.Length ==> users[i].id == n
}

method Main()
{
    var t := new Test;
    t.Init(3);
    var u1 := new User.Init(1,23);
    var u2 := new User.Init(2,24);
    var u3 := new User.Init(3,25);
    t.AddUser(u1);
    t.AddUser(u2);
    t.AddUser(u3);
}
}

class User {

   var id : int;
   var phone : int;

   method Init(i : int, p : int)
   modifies this`id, this`phone;
   requires 0 < i < 99999;
   requires 0 < p < 99999;
   ensures id == i;
   ensures phone == p;
   {
        id := i;
        phone := p;
   }
}