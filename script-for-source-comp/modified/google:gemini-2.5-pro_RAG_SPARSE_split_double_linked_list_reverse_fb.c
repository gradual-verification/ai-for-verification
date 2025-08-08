

typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;


typedef struct dllist {
	node head;
	node tail;
} *dllist;




void reverse(dllist arg)
{
	node orig_head = arg->head;
	node orig_tail = arg->tail;

	node ptr = arg->head;
	node prev = 0;
	node temp1 = 0;
	node temp2 = 0;
	while (ptr != 0)
	{

		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;


		prev = ptr;
		ptr = temp1;
	}



	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;

}
