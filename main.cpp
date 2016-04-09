//
//  main.cpp
//  kotzig_solver
//
//  Created by Thomas Yata on 2016/02/17.
//  Copyright © 2016年 Thomas Yata. All rights reserved.
//


#include <iostream>
#include <vector>
#include <algorithm>
const int N = 9;

//template <int n>
//struct fact{
//    enum { value = n * fact<n-1>::value };
//};
//template<>
//struct fact<0>{
//    enum { value = 1 };
//};
//const int M = fact<N>::value; //example
//const int N = M/2;

constexpr int fact(int n)
{
    int all_hs=1;
    for(int i=1;i<=n;i++){
        all_hs=all_hs*i;
    }
    return all_hs;
}
const int NumOfHamilton = fact(N-1)/2;
const int NumOf2uint=N*(N-1)*(N-2)/2/64+1;
const int NumOf1uint=N*(N-1)/2/64+1;
const int DudeneySize=(N-1)*(N-2)/2;
const int HDecSize=(N-1)/2;
const int NumOfHDec=N-2;


const int Max_HS_Per_1pass_MinBit=fact(N-2);
const int Max_HS_Per_2pass_MinBit=fact(N-3);
const int NumOf_1pass_Minbit=(N-2);
//const int NumOf_2pass_Minbit=(N-1)*(N-2);

const int Cut_until_step1=8; //0<Cut_until_step<DudeneySize now's best 3,7 38sec
const int Cut_until_step2=0;


uint64_t Call=0;
int Count[NumOfHDec];



void normalize(const int h[],int g[])
{
    int i,j;//hの0の位置を
    for(i=0;h[i]!=0;i++);//h[i]==0で停止
    for(j=0;j<N;j++) g[j]=h[(i+j)%N];
    if(g[1]>g[N-1]) std::reverse(g+1, g+N);//N-1までのひっくり返しだけど、これはSTLの癖のようなもので+1で指定
}
int cmp(const int h[],const int g[])
{
    int i;
    for (i=0; i<N; i++) {
        if(h[i]<g[i]) return -1;
        if(h[i]>g[i]) return 1;
    }
    return 0;
}
bool is_normal(const int hd_no ,const int H[][N])
{
    int i,j,k,d,sigma[N];
    int g[hd_no*HDecSize][N];
    std::vector<std::vector<std::vector<int>>> f(hd_no,std::vector<std::vector<int>>(HDecSize,std::vector<int>(N)));
    for (i=0; i<hd_no*HDecSize; i++) {
        for (d=0; d<N; d++) {
            //hs[i]をd,d+1,d+2,d+3.....に移す置換を作成
            for (j=0; j<N; j++) sigma[H[i][j]]=(d+j)%N;
            //関数sigmaに従って全てをgに写像する
            for (j=0; j<hd_no*HDecSize; j++) for (k=0; k<N; k++) g[j][k]=sigma[H[j][k]];
            //g[][]の各ハミルトンサイクルを標準形にしてfに入れる
            for(j=0;j<hd_no;j++) for(k=0;k<HDecSize;k++) normalize(g[j*HDecSize+k],&f[j][k][0]);
            //fのsets of HCの中身をソート
            for(j=0;j<hd_no;j++) std::sort(f[j].begin(), f[j].end());
            //fのset of sets of HCをソート
            std::sort(f.begin(), f.end());
            //hsとfの比較
            // f<hs ⇒ hsは標準形でない
            for (j=0; j<hd_no*HDecSize; j++) {
                k=cmp(H[j], &f[j/HDecSize][j%HDecSize][0]);
                if(k==1) return false;
                else if(k==-1) goto next1;
            }
        next1:;
        }
        for (d=0; d<N; d++) {
            //hs[i]をd,d-1,d-2,d-3.....に移す置換を作成
            for (j=0; j<N; j++) sigma[H[i][j]]=(d-j+N)%N;
            //関数sigmaに従って全てをgに写像する
            for (j=0; j<hd_no*HDecSize; j++) for (k=0; k<N; k++) g[j][k]=sigma[H[j][k]];
            //g[][]の各ハミルトンサイクルを標準形にしてfに入れる
            for(j=0;j<hd_no;j++) for(k=0;k<HDecSize;k++) normalize(g[j*HDecSize+k],&f[j][k][0]);
            //fのsets of HCの中身をソート
            for(j=0;j<hd_no;j++) std::sort(f[j].begin(), f[j].end());
            //fのset of sets of HCをソート
            std::sort(f.begin(), f.end());
            //hsとfの比較
            // f<hs ⇒ hsは標準形でない
            for (j=0; j<hd_no*HDecSize; j++) {
                k=cmp(H[j], &f[j/HDecSize][j%HDecSize][0]);
                if(k==1) return false;
                else if(k==-1) goto next2;
            }
        next2:;
        }
    }
    return true;
}

bool is_normal(const int hd_no,const int hs_itrs[DudeneySize],const int hs[NumOfHamilton][N]){
    int h[hd_no*HDecSize][N];
    for (int i=0; i<hd_no*HDecSize; i++) {
        for (int j=0; j<N; j++)
            h[i][j]=hs[hs_itrs[i]][j];
    }
    if (is_normal(hd_no, h)==1) return true;
    else return false;
}
void recursion(int lv, int& hn, bool vflg[N], int h[N], int hs[][N]){
    if ( lv==N && h[1]<h[N-1]){
        //再帰で完成した結果をhsに記入
        for (int j=0; j<N; j++) hs[hn][j]=h[j];
        hn++;
    }
    else{
        for (int i=1;i<N; i++) if(vflg[i]==0){
            h[lv]=i;
            vflg[i]=1;
            recursion(lv+1, hn, vflg, h, hs);
            vflg[i]=0;
            h[lv]=0;
        }
    }
}

void fill_hs(int hs[][N]){
    bool vflg[N];
    int h[N];
    //０初期化
    for (int i=0;i<NumOfHamilton; i++) {
        for (int j=0; j<N; j++) {
            hs[i][j]=0;
        }
    }
    for (int i=0; i<N; i++){
        vflg[i]=false;
        h[i]=0;
    }
    //初期値の代入
    vflg[0]=true;
    int hn=0;
    //再帰呼び出し
    recursion(1, hn, vflg, h, hs);
    if(hn==NumOfHamilton)printf("end_make_full_hs\n");
    else printf("error rec1\n");
}

void fill_1p_bf(const int hs[][N],const int f[N][N],uint64_t bf[][NumOf1uint])
{
    for (int i=0; i<NumOfHamilton; i++) {
        for (int j=0; j<N; j++) {
            const int l=hs[i][j];
            const int m=hs[i][(j+1)%N];
            //// 0011000011110010 |= 0000100000000000のようなイメージ
            bf[i][f[l][m]/64] |= (1ULL<<f[l][m]%64);
        }
    }
}

void fill_2p_bf(const int hs[][N],const int f[][N][N],uint64_t bf[][NumOf2uint])
{
    for (int i=0; i<NumOfHamilton; i++) {
        for (int j=0; j<N; j++) {
            const int l=hs[i][j];
            const int m=hs[i][(j+1)%N];
            const int n=hs[i][(j+2)%N];
            //// 0011000011110010 |= 0000100000000000のようなイメージ
            bf[i][f[l][m][n]/64] |= (1ULL<<f[l][m][n]%64);
        }
    }
}

bool are_1pass_disjoint(const uint64_t bf_a[NumOf1uint],const uint64_t bf_b[NumOf1uint])
{
    for (int i=0; i<NumOf1uint; i++) if ((bf_a[i] & bf_b[i])!=0) return 0;
    return true;
}

bool are_2pass_disjoint(const uint64_t bf_a[NumOf2uint],const uint64_t bf_b[NumOf2uint])
{
    for (int i=0; i<NumOf2uint; i++) if ((bf_a[i] & bf_b[i])!=0) return 0;
    return true;
}


void bit_set_1(uint64_t check_bf[NumOf1uint],const uint64_t bf[NumOf1uint])
{
    for (int i=0; i<NumOf1uint; i++) check_bf[i] |= bf[i];
}
void bit_set_2(uint64_t check_bf[NumOf2uint],const uint64_t bf[NumOf2uint])
{
    for (int i=0; i<NumOf2uint; i++) check_bf[i] |= bf[i];
}

void bit_reset_1(uint64_t check_bf[NumOf1uint],const uint64_t bf[NumOf1uint])
{
    for (int i=0; i<NumOf1uint; i++) check_bf[i] &= ~bf[i];
}
void bit_reset_2(uint64_t check_bf[NumOf2uint],const uint64_t bf[NumOf2uint])
{
    for (int i=0; i<NumOf2uint; i++) check_bf[i] &= ~bf[i];
}


int ntz(uint64_t bf){
    int n;
    if(bf==0)return 64;
    n=1;
    if((bf & 0x00000000ffffffffULL)==0){ n = n + 32 ; bf = bf >> 32;}
    if((bf & 0x000000000000ffffULL)==0){ n = n + 16 ; bf = bf >> 16;}
    if((bf & 0x00000000000000ffULL)==0){ n = n + 8 ; bf = bf >> 8;}
    if((bf & 0x000000000000000fULL)==0){ n = n + 4 ; bf = bf >> 4;}
    if((bf & 0x0000000000000003ULL)==0){ n = n + 2 ; bf = bf >> 2;}
    return n -(bf & 1ULL);
}

int array_nt1(const uint64_t bf[NumOf1uint]){
    int cnt=0;
    for(int i=0;i<NumOf1uint;i++){
        int j=ntz(~bf[i]);
        if(j<64)return cnt+j;
        else cnt+=64;
    }
    return 0;
}

void extract(int size_extracted_minbit[Max_HS_Per_1pass_MinBit],
             uint64_t extracted_1pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf1uint],
             uint64_t extracted_2pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf2uint],
             int extracted_hs[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][N],
             const int size_of_1pass_minbit[Max_HS_Per_1pass_MinBit],
             const uint64_t check_2bf[NumOf2uint],
             const uint64_t classified_1pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf1uint],
             const uint64_t classified_2pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf2uint],
             const int classified_hs[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][N])
{
    for (int i=0; i<NumOf_1pass_Minbit; i++) {
        for (int j=0; j<size_of_1pass_minbit[i]; j++) {
            //もしcheck_bfと素であれば
            if (are_2pass_disjoint(check_2bf, classified_2pass_bf[i][j])==1) {
                for (int k=0; k<N; k++) extracted_hs[i][size_extracted_minbit[i]][k]=classified_hs[i][j][k];
                for (int k=0; k<NumOf1uint; k++) extracted_1pass_bf[i][size_extracted_minbit[i]][k]=classified_1pass_bf[i][j][k\
                                                                                                                              ];
                for (int k=0; k<NumOf2uint; k++) extracted_2pass_bf[i][size_extracted_minbit[i]][k]=classified_2pass_bf[i][j][k\
                                                                                                                              ];
                size_extracted_minbit[i]++;
            }
        }
    }
}
void rec(int hd_no,int level,int dude[][N],uint64_t check_1bf[][NumOf1uint],uint64_t check_2bf[NumOf2uint],
         const int size_of_1pass_minbit[Max_HS_Per_1pass_MinBit],
         const uint64_t classified_1pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf1uint],
         const uint64_t classified_2pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf2uint],
         const int classified_hs[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][N])
{
    Call++;
    //if (Call==100000)exit (0);
    if ( hd_no ==
        //2
        NumOfHDec
        ){
        if(is_normal(hd_no, dude)){
            if(Count[hd_no-1]%100==0)std::cout<<"No."<<Count[hd_no-1]<<std::endl;
        }
    }
    else{
        //最右の0の位置を探して代入
        int current_minbit=array_nt1(check_1bf[hd_no]);
        //現在の最小ビット群の全てのビットを検討
        for (int i=0; i<size_of_1pass_minbit[current_minbit]; i++) {
            //互いに素であれば
            if (are_2pass_disjoint(check_2bf, classified_2pass_bf[current_minbit][i])
                && are_1pass_disjoint(check_1bf[hd_no], classified_1pass_bf[current_minbit][i])) {
                bit_set_1(check_1bf[hd_no], classified_1pass_bf[current_minbit][i]);
                bit_set_2(check_2bf, classified_2pass_bf[current_minbit][i]);
                for (int j=0; j<N; j++)dude[hd_no*HDecSize+level][j]=classified_hs[current_minbit][i][j];
                if (level == HDecSize-1) {
                    if (is_normal(hd_no+1,dude)==true) Count[hd_no]++;
                    if ( hd_no*HDecSize+level <Cut_until_step1
                        //|| hd_no==Cut_until_step2
                        ){
                        //配列を用意して、初期化
                        int extracted_hs[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][N];
                        uint64_t extracted_1pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf1uint];
                        uint64_t extracted_2pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf2uint];
                        std::fill_n(extracted_hs[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*N, 0);
                        std::fill_n(extracted_1pass_bf[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*NumOf1uint, 0);
                        std::fill_n(extracted_2pass_bf[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*NumOf2uint, 0);
                        int size_extracted_minbit[Max_HS_Per_1pass_MinBit];
                        std::fill_n(size_extracted_minbit,Max_HS_Per_1pass_MinBit,0);
                        extract(size_extracted_minbit,extracted_1pass_bf,extracted_2pass_bf,extracted_hs,size_of_1pass_minbit,check_2bf,classified_1pass_bf,classified_2pass_bf,classified_hs);
                        rec(hd_no+1,0,dude,check_1bf,check_2bf,size_extracted_minbit,extracted_1pass_bf,extracted_2pass_bf,extracted_hs);
                    }
                    else rec(hd_no+1,0,dude,check_1bf,check_2bf,size_of_1pass_minbit,classified_1pass_bf,classified_2pass_bf,classified_hs);
                    //テストコード
                    if(hd_no==0){
                        std::cout<<"Call    "<<Call<<std::endl;
                        for(int i=0;i<NumOfHDec;i++)std::cout<<"Count "<<i<<" "<<Count[i]<<std::endl;
                        exit(0);
                    }
                }
                else if(hd_no>0 || level == 0){
                    if(cmp(dude[hd_no*HDecSize], dude[(hd_no-1)*HDecSize])==1){
                        rec(hd_no,level+1,dude,check_1bf,check_2bf,size_of_1pass_minbit,classified_1pass_bf,classified_2pass_bf,classified_hs);
                    }
                }
                else rec(hd_no,level+1,dude,check_1bf,check_2bf,size_of_1pass_minbit,classified_1pass_bf,classified_2pass_bf,classified_hs);

                for (int j=0; j<N; j++)dude[hd_no*HDecSize+level][j]=0;
                bit_reset_1(check_1bf[hd_no], classified_1pass_bf[current_minbit][i]);
                bit_reset_2(check_2bf, classified_2pass_bf[current_minbit][i]);
            }
        }
    }
}

void printh(const int v[][N])
{
    printf("hs\n");
    for(int i=0;i<NumOfHamilton;i++){
        for(int j=0;j<N;j++){
            printf("%d",v[i][j]);
        }
        printf("\n");
    }
    printf("\n");
}


bool the_bit_is_1(const int a,const uint64_t bf[])
{
    if((bf[a/64] & (1LLU << a%64))!=0) return true;
    return false;
}

int main(void) {
    //グローバル配列変数の初期化
    for(int i=0;i<NumOfHDec;i++) Count[i]=0;
    
    //最小bitごと別々の配列に格納するための配列の用意と初期化
    int classified_hs[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][N];
    uint64_t classified_1pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf1uint];
    uint64_t classified_2pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf2uint];
    std::fill_n(classified_hs[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*N, 0);
    std::fill_n(classified_1pass_bf[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*NumOf1uint, 0);
    std::fill_n(classified_2pass_bf[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*NumOf2uint, 0);
    
    //hsの最小ビット配列の個数を有する配列を定義し初期化
    int size_of_1pass_minbit[NumOf_1pass_Minbit];
    std::fill_n(size_of_1pass_minbit, NumOf_1pass_Minbit, 0);
    
    
    {
        //ハミルトンサイクルの集合Hのすべての要素hiを生成
        int hs[NumOfHamilton][N];
        fill_hs(hs);
        //        printh(hs);
        
        //2pass用と1pass用bfを用意し、初期化
        uint64_t one_pass_bf[NumOfHamilton][NumOf1uint];
        uint64_t two_pass_bf[NumOfHamilton][NumOf2uint];
        std::fill_n(one_pass_bf[0], NumOfHamilton*NumOf1uint, 0);
        std::fill_n(two_pass_bf[0], NumOfHamilton*NumOf2uint, 0);
        
        //1-passとビットの位置に相当する対応表を作る
        int f1[N][N],l=0;
        for (int a=0; a<N-1; a++) for (int b=a+1; b<N; b++) if(a!=b){
            f1[a][b]=l;
            f1[b][a]=l;
            l++;
        }
        //2-passとビットの位置に相当する対応表を作る
        int f2[N][N][N];
        l=0;
        for (int a=0; a<N-1; a++) for (int b=0; b<N; b++) if(b!=a) for (int c=a+1; c<N; c++) if(b!=c){
            f2[a][b][c]=l;
            f2[c][b][a]=l;
            l++;
        }
        //それぞれのhsの1pass,2passをbfに格納
        fill_1p_bf(hs,f1,one_pass_bf);
        fill_2p_bf(hs,f2,two_pass_bf);
        
        //hsとbfをそれぞれclassified_hsとclassified_bfに最小bitごと格納し、カウント
        for (int i=0,lv=0; i<NumOfHamilton; i++) {
            if(the_bit_is_1(lv,one_pass_bf[i])){
                for (int j=0; j<N; j++) classified_hs[lv][size_of_1pass_minbit[lv]][j]=hs[i][j];
                for (int j=0; j<NumOf1uint; j++) classified_1pass_bf[lv][size_of_1pass_minbit[lv]][j]=one_pass_bf[i][j];
                for (int j=0; j<NumOf2uint; j++) classified_2pass_bf[lv][size_of_1pass_minbit[lv]][j]=two_pass_bf[i][j];
                size_of_1pass_minbit[lv]++;
            }
            else {
                lv++;
                i--;
            }
        }
    }
    //2pass用と1pass用bfを用意し、初期化
    uint64_t check_1bf[NumOfHDec][NumOf1uint];
    uint64_t check_2bf[NumOf2uint];
    std::fill_n(check_1bf[0], NumOfHDec*NumOf1uint, 0);
    std::fill_n(check_2bf, NumOf2uint, 0);
    //対応するhsのイテレータを記録しておく配列hs_itrsを用意
    int dude[DudeneySize][N];
    std::fill_n(dude[0], DudeneySize*N, 0);
    //初期値0123456代入
    for (int i=0; i<N; i++) {
        dude[0][i]=i;
    }
    bit_set_1(check_1bf[0], classified_1pass_bf[0][0]);
    bit_set_2(check_2bf, classified_2pass_bf[0][0]);
    
    int extracted_hs[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][N];
    uint64_t extracted_1pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf1uint];
    uint64_t extracted_2pass_bf[NumOf_1pass_Minbit][Max_HS_Per_1pass_MinBit][NumOf2uint];
    std::fill_n(extracted_hs[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*N, 0);
    std::fill_n(extracted_1pass_bf[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*NumOf1uint, 0);
    std::fill_n(extracted_2pass_bf[0][0], NumOf_1pass_Minbit*Max_HS_Per_1pass_MinBit*NumOf2uint, 0);
    int size_extracted_minbit[Max_HS_Per_1pass_MinBit];
    std::fill_n(size_extracted_minbit,Max_HS_Per_1pass_MinBit,0);
    extract(size_extracted_minbit,extracted_1pass_bf,extracted_2pass_bf,extracted_hs,size_of_1pass_minbit,check_2bf,classified_1pass_bf,classified_2pass_bf,classified_hs);
    rec(0,1,dude,check_1bf,check_2bf,size_extracted_minbit,extracted_1pass_bf,extracted_2pass_bf,extracted_hs);
    
    std::cout<<"end     "<<std::endl;
    std::cout<<"Call    "<<Call<<std::endl;
    for(int i=0;i<NumOfHDec;i++)std::cout<<"Count "<<i<<" "<<Count[i]<<std::endl;
    
    return 0;
}


