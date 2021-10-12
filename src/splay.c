#include <stddef.h>

typedef struct node {unsigned long key; void* value; struct node *left; struct node *right; struct node *parent; } node;

void rotate(node **root, node *x) {
  struct node *p, *ch;
  p = x->parent;
  if (p->left == x) {
    p->left = x->right;
    x->right = p;
    if (p->left) {
      p->left->parent = p;
    }
  } else {
    p->right = x->left;
    x->left = p;
    if (p->right) {
      p->right->parent = p;
    }
  }
  if (p->parent) {
    if (p->parent->left == p) {
      p->parent->left = x;
    } else {
      p->parent->right = x;
    }
  } else {
    *root = x;
  }
  x->parent = p->parent;
  p->parent = x;
}


void splay (struct node **root, struct node *x) {
  struct node *p, *g;
  while (1) {
    p = x->parent;
    if (p == NULL) {
      return;
    }
    g = p->parent;
    if (g == NULL) {
      rotate(root, x);
      return;
    }
    if ((p->left == x) == (g->left == p)) {
      rotate(root, p);
      rotate(root, x);
    } else {
      rotate(root, x);
      rotate(root, x);
    }
  }
}
