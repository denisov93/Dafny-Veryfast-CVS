/*@
predicate Positive(unit a, int v; unit b) = v >= 0 &*& b == unit;

predicate Inv(Queue q;) = 
	q.buffer |-> ?a
	&*& q.n |-> ?v
	&*& 0 <= v
	&*& v <= a.length
	&*& array_slice_deep(a,0,v,Positive,unit,_,_)
	&*& array_slice(a,v,a.length,_);
@*/

//Queue based on a circular buffer.
class Queue {
    int buffer[];
    int n;
  
    //creates a new Queue with capacity max.
    Queue(int max){}
  
    //places the int v at the end of this Queue
    void enqueue(int x)
    //@ requires Inv(this) &*& x >= 0;
    //@ ensures Inv(this);
    {
        if(n< buffer.length){
            buffer[n++] = x;
            //@ assert this.n |-> ?v &*& this.buffer |-> ?a;
            //@ array_slice_deep_close(a,v-1,Positive,unit);
            //@ array_slice_deep_join(a,0);
            //@ assert array_slice_deep(a,0,v,Positive,unit,_,_);
        }
    }
  
    //retrieves the element at the start of this Queue.
    int dequeue(){}
    
    //returns true if this Queue has reached its capacity.
    boolean isFull(){}
    
    //returns true if this Queue has no elements.
    boolean isEmpty(){}
  
  }