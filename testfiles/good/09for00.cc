int main() {
    int y = 5 ;
    int x = 4 ;

    for (int i=x; i>0; --i) {
        y = y + i ;
        printInt(y) ;
    }
    printInt(x) ;
    printInt(y) ;

    return 0 ;
}
