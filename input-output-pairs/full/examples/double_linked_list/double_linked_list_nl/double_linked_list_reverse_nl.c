/*

Full functional correctness proof of doubly-linked list reversal
Stephan van Staden, 2009

*/


typedef struct node {
	int item;
	struct node *next;
	struct node *prev;

// TODO: make this function pass the verification
/***
 * Description:
 * The `reverse` function reverses the doubly linked list.
 *
 * @param arg: the head of a given doubly linked list
 * 
 * The function ensures that the doubly linked list has its values reversed.
 */
void reverse(dllist arg)
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	while (ptr != 0)
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		ptr = temp1;
	}
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}