import java.util.concurrent.locks.*;

/*@
predicate Valid(unit a, A o; unit b) = o != null &*& AInv(o) &*& b == unit;

predicate AInv(A o;) = o.a |-> ?v &*& v >= 0;

predicate QueueInv(Queue q; int n, int m) = 
	q.input |-> ?a
    &*& q.output |-> ?b
    &*& a != null
    &*& b != null
    &*& q.numelements |-> n
    //pode escrever e ler na pos de vetor 
    &*& m == a.length
    &*& a.length == b.length
    &*& q.in_n |-> ?h
    &*& q.out_n |-> ?t
    &*& 0 <= h &*& h <= a.length
    &*& 0 <= t &*& t <= b.length
    &*& h+t == n 
    &*& h+t <= m
    &*& n >= 0 
    
    &*& array_slice_deep(a,0,h,Valid, unit, ?in, _)
    &*& array_slice(a, h, a.length, ?out2)
    
    //&*& array_slice(b,0,b.length,?out3)
    &*& array_slice(b, t, b.length, ?out4)
    &*& array_slice_deep(b,0,t,Valid, unit, ?in2, _)
    	
       
    ; 
@*/

class A{
    int a;
    
    public A(int a)
    //@ requires a >= 0;
    //@ ensures AInv(this);
    {
	    this.a = a;
    }
}


//Queue based on a circular buffer.
class Queue {
    A[] input;
    A[] output;
    int numelements;
    int in_n;
    int out_n;
  
    //creates a new Queue with capacity max.
    Queue(int size)
    
    //@ requires size > 0;
    //@ ensures QueueInv(this,0,size);
    {
        input = new A[size];
        output = new A[size];
        numelements = 0;
        in_n = 0;
        out_n = 0;
    }
  
    //places the int v at the end of this Queue
    void enqueue(A v)
    //@ requires QueueInv(this,?n,?m) &*& v!=null &*& AInv(v) &*& n < m;
    //@ ensures QueueInv(this,n+1,m);
    {
        input[in_n++] = v;

        numelements++;
    }
  
    //retrieves the element at the start of this Queue.
    A dequeue()
    //@ requires QueueInv(this,?n,?m) &*& n>0;
    //@ ensures QueueInv(this,n-1,m) &*& result != null &*& AInv(result);
    {
        
        if (out_n == 0){
                flush();
            }
	
            A v = output[out_n];
            output[out_n] = null;
            out_n--;
            numelements--;
            
            return v ;   
        
    }
    
    //returns true if this Queue has reached its capacity.
    boolean isFull()
    //@ requires QueueInv(this,?n,?m);
    //@ ensures QueueInv(this,n,m) &*& result == (n==m);
    {
        return numelements== input.length;
    }
    
    //returns true if this Queue has no elements.
    boolean isEmpty()
    //@ requires QueueInv(this,?n,?m);
    //@ ensures QueueInv(this,n,m) &*& result == (n==0);
    {
        return numelements == 0;
    }
  
    void flush()
    //@ requires QueueInv(this,?n,?m) ;
    //@ ensures QueueInv(this,n,m) ;
    {
        
        while (in_n > 0)
        //@ invariant QueueInv(this,n,m);
        {
            output[out_n] = input[in_n-1];
            in_n-=1;
            out_n+=1;
            
        }
        
    }
    
  }

/*@
predicate_ctor CQueueSharedState(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, _, _);

predicate_ctor CQueueSharedState_notempty(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, ?n, _) &*& n > 0;

predicate_ctor CQueueSharedState_notfull(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, ?n, ?m) &*& n < m;

predicate CQueueInv(CQueue c;) = 
            c.mon |-> ?l
        &*& l != null
        &*& lck(l, 1, CQueueSharedState(c))

        &*& c.notempty |-> ?c1
        &*& c1 != null
        &*& cond(c1, CQueueSharedState(c), CQueueSharedState_notempty(c))

        &*& c.notfull |-> ?c2
        &*& c2 != null
        &*& cond(c2, CQueueSharedState(c), CQueueSharedState_notfull(c))
        ;
@*/

class CQueue {
    Queue q;
    ReentrantLock mon;
    Condition notempty;
    Condition notfull;

    CQueue(int size)
    //@ requires size > 0;
    //@ ensures CQueueInv(this);
    {
        q = new Queue(size);
        //@ close CQueueSharedState(this)();
        //@ close enter_lck(1, CQueueSharedState(this));
        mon = new ReentrantLock();
        //@ close set_cond(CQueueSharedState(this), CQueueSharedState_notempty(this));
        notempty = mon.newCondition();
        //@ close set_cond(CQueueSharedState(this), CQueueSharedState_notfull(this));
        notfull = mon.newCondition();
    }

      void enqueue(A v)
      //@ requires [?f]CQueueInv(this) &*& v != null &*& AInv(v);
      //@ ensures [f]CQueueInv(this);
      {
          mon.lock();
          if(q.isFull()){
                notfull.await();
                //@ open CQueueSharedState_notfull(this)();
          }
          //@ open QueueInv(q,_,_);
          q.enqueue(v);
          notempty.signal();
          mon.unlock();
      }

      A dequeue()
      //@ requires [?f]CQueueInv(this);
      //@ ensures [f]CQueueInv(this);
      {
          mon.lock();
          if( q.isEmpty()){
                notempty.await();
                //@ open CQueueSharedState_notempty(this)();
          }
          //@ open QueueInv(q,_,_);
          A v = q.dequeue();
          notfull.signal();
          mon.unlock();
          return v;
      }
  }

/*@
    predicate ProducerInv(Producer p;) = 
            p.q |-> ?q
        &*& q != null 
        &*& [_]CQueueInv(q)
        &*& p.id |-> ?v
        &*& v >= 0
        ;
@*/

/*@
    predicate ConsumerInv(Consumer c;) = 
            c.q |-> ?q
        &*& q != null 
        &*& [_]CQueueInv(q)
        &*& c.id |-> ?v
        &*& v >= 0
        ;
@*/

//@predicate frac(real f) = true;



class Producer implements Runnable{
    CQueue q;
    int id;

    //@ predicate pre() = ProducerInv(this);
    //@ predicate post() = emp;
    public Producer(CQueue q, int id)
    //@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0;
    //@ ensures ProducerInv(this);
    {
        this.q = q;
        this.id = id;
    }

    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        while(true)
        //@ invariant ProducerInv(this);
        {
            A a = new A(id);
            q.enqueue(a);
            //System.out.println(id);
         
            //try {
            //	Thread.sleep(100);
	    //} catch (InterruptedException e) {
            //e.printStackTrace();
	    //}
        }
    }
}

class Consumer implements Runnable{
    CQueue q;
    int id;

    //@ predicate pre() = ConsumerInv(this);
    //@ predicate post() = emp;
    public Consumer(CQueue q, int id)
    //@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0;
    //@ ensures ConsumerInv(this);
    {
        this.q = q;
        this.id = id;
    }

    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        while(true)
        //@ invariant ConsumerInv(this);
        {
            A a = q.dequeue();
            
            //try {
            //	Thread.sleep(100);
	    //} catch (InterruptedException e) {
	    //e.printStackTrace();
	    //}
        }
    }
}

class ProducerConsumer {

    public static void main(String []args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
    {
        //System.out.println("...");
        CQueue q = new CQueue(10);
        //@ assert CQueueInv(q);
        //@ close frac(1);
        for( int i = 0; i < 10; i++ )
        //@ invariant 0 <= i &*& i <= 10 &*& frac(?f) &*& [f]CQueueInv(q) &*& System_out(?z) &*& z != null;
        {
            System.out.println("...");
            //@ open frac(f);
            //@ close frac(f/2);
            new Thread(new Producer(q,i)).start();
            //@ close frac(f/4);
            new Thread(new Consumer(q,100+i)).start();
            //@ close frac(f/4);
        }
    }

}