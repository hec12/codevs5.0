#include <bits/stdc++.h>

#define _overload(_1,_2,_3,name,...) name
#define _rep(i,n) _range(i,0,n)
#define _range(i,a,b) for(int i=int(a);i<int(b);++i)
#define rep(...) _overload(__VA_ARGS__,_range,_rep,)(__VA_ARGS__)

#define _rrep(i,n) _rrange(i,n,0)
#define _rrange(i,a,b) for(int i=int(a)-1;i>=int(b);--i)
#define rrep(...) _overload(__VA_ARGS__,_rrange,_rrep,)(__VA_ARGS__)

#define _all(arg) begin(arg),end(arg)
#define uniq(arg) sort(_all(arg)),(arg).erase(unique(_all(arg)),end(arg))
#define getidx(ary,key) lower_bound(_all(ary),key)-begin(ary)
#define clr(a,b) memset((a),(b),sizeof(a))
#define bit(n) (1LL<<(n))

//#define FUNC
//#define DEBUG
//#define SCORE
template<class T>bool chmax(T &a, const T &b) { return (a<b)?(a=b,1):0;}
template<class T>bool chmin(T &a, const T &b) { return (b<a)?(a=b,1):0;}

using namespace std;

const int H=17;
const int W=14;

const int INF = 100000010;
const char CELL_EMPTY = '_';
const char CELL_WALL ='W';
const char CELL_OBJECT = 'O';

const int DOG=1;
const int NINJA=2;
const int SOUL=3;
const int NINJA_EXCEPT_DOG=4;

// 17 14 32*16
//  5bit 4bit[0,32) [0,15)
#define X(x) ((x) & 15)                 // Unpacking
#define Y(y) ((y) >> 4)
#define XY(x,y) (((y) << 4) | (x))     // Packing

const int op[] = {292,291,290,289,288,283,282,281,280,275,274,273,272,267,266,265,264,259,258,257,256,219,218,217,216,211,210,209,208,203,202,201,200,194,193,192,155,154,153,152,147,146,145,144,139,137,136,131,130,129,128,91,90,89,88,83,82,80,75,74,73,72,67,66,65,64,27,26,25,19,18,17,16,11,10,9,8,3,2,1,0};
#define MOVE(x,i) ((op[x]>>(3*i))&7)

using Point=int;
// Point -> Integer 

random_device seed_gen;
mt19937 mt(seed_gen());

class Skill {
    public:
        int id, cost;
        Skill() { id = cost = -1; }
        Skill(int id, int cost): id(id), cost(cost) {}

        static Skill input(int id) {
            int cost;
            cin >> cost;
            return Skill(id, cost);
        }
};

class Cell{
    public:
        int xy;
        char kind;
        bool containsNinja, containsSoul, containsDog;
        Cell() {
            kind = '?';
            containsNinja = containsSoul = containsDog = false;
        }
        Cell(int x, int y, char kind):  kind(kind) {
            xy = XY(x,y);
            containsNinja = containsSoul = containsDog = false;
        }

        bool isWall() const { return kind == CELL_WALL; }
        bool isObject() const { return kind == CELL_OBJECT; }
        bool isEmpty() const { return kind == CELL_EMPTY; }
};

class Character{
    public:
        int id,xy;
        Character() { id = xy = -1; }
        Character(int id, int xy): id(id), xy(xy) {}
        Character(int id, int x, int y): id(id) { xy=XY(x,y);}

        static Character input() {
            int id, x, y;
            cin >> id >> y >> x;
            return Character(id, x, y);
        }
        bool operator== (const int &cxy) const { return xy == cxy; }
};

class State {
    public:
        int skillPoint;
        int number,upper;
        array<Cell,272> field;
        vector<Character> ninjas;
        vector<Character> avatars;
        vector<Character> dogs;
        vector<Point> souls;
        vector<int> skillCount;

        State(){
            number=2,upper=21;
            skillPoint = -1;
            ninjas.clear();
            dogs.clear();
            souls.clear();
            skillCount.clear();
        }

        static State input(int numOfSkills) {
            State st;
            string dummy;

            cin >> st.skillPoint;
            cin >> dummy >> dummy;

            rep(y,H){
                string s;
                cin >> s;
                rep(x,W) st.field[XY(x,y)]=Cell(x, y, s[x]);
            }

            int numOfNinjas;
            cin >> numOfNinjas;
            
            rep(i,numOfNinjas){
                Character ninja = Character::input();
                st.ninjas.emplace_back(ninja);
                st.field[ninja.xy].containsNinja = true;
            }

            int numOfDogs;
            cin >> numOfDogs;
            
            rep(i,numOfDogs){
                Character dog = Character::input();
                st.dogs.emplace_back(dog);
                st.field[dog.xy].containsDog = true;
            }

            int numOfSouls;
            cin >> numOfSouls;
        
            rep(i,numOfSouls){
                int x,y;
                cin >> y >> x;
                st.souls.emplace_back(XY(x, y));
                st.field[XY(x,y)].containsSoul = true;
            }

            rep(i,numOfSkills){
                int count;
                cin >> count;
                st.skillCount.emplace_back(count);
            }

            return st;
        }
};

const int dx[] =    {  0,  -1,   1,   0,   0,  1, -1 , 1, -1};
const int dy[] =    { -1,   0,   0,   1,   0,  1,  1, -1, -1};
const int dxy[] =   {-16,  -1,   1,  16,   0, 17, 15,-15,-17};
const string ds[] = {"U", "L", "R", "D", "N"};

const int turn_limit=300;
int turn=0,remTime[turn_limit];
vector<Skill> skills;
State myState[turn_limit]; 
bool my_checkmate=false;

int myScore[turn_limit];
State rivalState[turn_limit];
int rivalScore[turn_limit];
bool rival_checkmate=false;

int critical_skill[8];


using Dist=array<int,272>;

#define PUSH(v) (queue[tail++]=v) 
#define POP() (queue[head++])

Dist bfs(const State &board,int type){
    #ifdef FUNC
        cerr << "BFS" << " " << type << endl;
    #endif

    Dist dist;
    int queue[512],head=0,tail=0;

    switch(type){
        case DOG:
            dist.fill(INF);
            for(auto &dog:board.dogs){
                PUSH(dog.xy);
                dist[dog.xy]=0;
            }
            while(head!=tail){
                const int cxy=POP();
                rep(dir,4){
                    const int nxy=cxy+dxy[dir];
                    if(board.field[nxy].isEmpty()==false) continue;
                    if(chmin(dist[nxy],dist[cxy]+1)) PUSH(nxy);
                }
            }
            break;
        case NINJA:
            dist.fill(INF);
            for(auto &ninja:board.ninjas){
                PUSH(ninja.xy);
                dist[ninja.xy]=0;
            }
            while(head!=tail){
                const int cxy=POP();
                rep(dir,4){
                    const int nxy=cxy+dxy[dir];
                    if(board.field[nxy].isEmpty()==false) continue;
                    if(chmin(dist[nxy],dist[cxy]+1)) PUSH(nxy);
                }
            }
            break;
        case SOUL:
            dist.fill(INF);
            for(auto &soul:board.souls){
                PUSH(soul);
                dist[soul]=(board.field[soul].isObject())?10:0;
            }
            while(head!=tail){
                const int cxy=POP();
                rep(dir,4){
                    const int nxy=cxy+dxy[dir];
                    if(board.field[nxy].isEmpty()==false) continue;
                    if(chmin(dist[nxy],dist[cxy]+1)) PUSH(nxy);
                }
            }
            break;

        case NINJA_EXCEPT_DOG:
            dist.fill(0);
            rep(id,2){
                Dist tmp;
                tmp.fill(INF);
                PUSH(board.ninjas[id].xy);
                tmp[board.ninjas[id].xy]=0;
                while(head!=tail){
                    const int cxy=POP();
                    rep(dir,4){
                        const int nxy=cxy+dxy[dir];
                        if(board.field[nxy].isEmpty()==false) continue;
                        if(board.field[nxy].containsDog) continue;
                        if(chmin(dist[nxy],dist[cxy]+1)) PUSH(nxy);
                    }
                }
                rep(y,1,H)rep(x,1,W) chmax(dist[XY(x,y)],tmp[XY(x,y)]);
            }
            break;
    }    
    return dist;
}


bool simulateWalk(State &board,int id, int dir){
    if(dir==4) return true;
    const int nxy = board.ninjas[id].xy + dxy[dir];
    if(board.field[nxy].isWall()) return false;
 
    const int n2xy=nxy+dxy[dir];
    

    if(board.field[nxy].isObject()){
        // 岩を押したときの判定は空きマス以外にも条件がある．
        if(board.field[n2xy].isEmpty()==false) return false;
        // 忍犬の判定も忘れない．
        if(board.field[n2xy].containsDog) return false;       
        // 忍者の判定も忘れない．
        if(board.field[n2xy].containsNinja) return false;       

        board.field[n2xy].kind=CELL_OBJECT;
        board.field[nxy].kind=CELL_EMPTY;
    }

    //　移動
    board.field[board.ninjas[id].xy].containsNinja=false;
    board.ninjas[id].xy = nxy;
    board.field[board.ninjas[id].xy].containsNinja=true;
    
    if(board.field[nxy].containsSoul){
        // 忍力回復
        board.skillPoint+=2;

        // フィールドのフラグをfalseに
        board.field[nxy].containsSoul=false;

        // 取得済みのソウルの座標削除
        board.souls.erase(remove(_all(board.souls),nxy),end(board.souls));
    }

    return true;
}

void simulateTurn(State &board){
    //分身対応
    bool changed=false;
    if(board.avatars.empty()==false){
        swap(board.ninjas,board.avatars);
        changed=true;
    }

    Dist dist = bfs(board,NINJA);
    sort(_all(board.dogs),
        [&](const Character& a, const Character& b){
            int da=dist[a.xy],db=dist[b.xy];
            return (da==db)?a.id<b.id:da<db;
        }
    );
    
    for(auto &dog:board.dogs){
        rep(dir,4){
            int nxy = dog.xy + dxy[dir];
            if(dist[dog.xy]!=dist[nxy]+1) continue;
            if(board.field[nxy].containsDog) continue;
            board.field[dog.xy].containsDog=false;
            dog.xy=nxy;
            board.field[dog.xy].containsDog=true;
            dir=4; // ループ脱出
        }
    }

    //分身対応
    if(changed){
        swap(board.ninjas,board.avatars);
        board.avatars.clear();
    }

    board.number=2,board.upper=21;
    return;
}

void simulateDog(State &board,int num){

    Dist dist = bfs(board,NINJA);
    rep(loop,num){
        int cmax=0;
        rep(y,1,H-1)rep(x,1,W-1){
            const int cxy=XY(x,y);
            if(dist[cxy]==INF) continue;
            if(board.field[cxy].containsDog) continue;
            chmax(cmax,dist[cxy]);
        }

        rep(y,1,H-1)rep(x,1,W-1){
            const int cxy=XY(x,y);
            if(cmax!=dist[cxy])  continue;
            if(board.field[cxy].containsDog) continue;
            int last=0;
            if(board.dogs.empty()==false) last=board.dogs[int(board.dogs.size())-1].id;
            board.dogs.emplace_back(Character(last+1,cxy));
            board.field[cxy].containsDog = true;
            y=H,x=W;
        }
    }
    
    return;
}

inline int simulateSkill(State &board,int skill,Point p,bool comsume=true){
    board.number=2,board.upper=21;
    if(skill!=-1 && comsume){
        if(board.skillPoint < skills[skill].cost) return false;  
        board.skillPoint-=skills[skill].cost;         
    }

    switch(skill){
        case 2:
        case 4:
        case 6:
            break;    
        case 0:
            board.number=3,board.upper=81;
            break;
        case 1:
            if(board.field[p].isEmpty()==false) return false;
            if(board.field[p].containsNinja) return false;
            if(board.field[p].containsDog) return false;
            board.field[p].kind=CELL_OBJECT;
            break;
        case 3:
            if(board.field[p].isObject()==false) return false;
            board.field[p].kind=CELL_EMPTY;       
            break;
        case 5:
            if(board.field[p].isEmpty()==false) return false;
            board.avatars.emplace_back(Character(0,p));
            break;
        case 7:
            const int cxy=board.ninjas[p].xy;
            int num=0;       
            rep(dir,9){
                const int nxy=cxy+dxy[dir];
                if(board.field[nxy].containsDog==false) continue;
                // フィールドのフラグをfalseに
                board.field[nxy].containsDog=false,num++;
                // 犬の座標削除
                board.dogs.erase(remove(_all(board.dogs),nxy),end(board.dogs));
            }
            return num;
            break;    
    }
    return true;
}

const int threshold=10;
const int threshold2=1000;
const int depth_limit=5;
using Operation=tuple<State,int,int,int,int,int,Point>;
vector<Operation> check[depth_limit+1];

int ninja_soul_prev[2];
int dummy[2]={-INF,-INF};

const int dog_coef=8000;
const int skiilpoint_coef=5000;

inline int score(const State &board,int ninja_soul_prev[2]){
    //1. 犬に追いつかれる -INF
    rep(id,2){
        const int cxy = board.ninjas[id].xy;
        if(board.field[cxy].containsDog) return -INF;
    }

    int res=0;
    Dist dist_dog = bfs(board,DOG);
    Dist dist_ninja = bfs(board,NINJA_EXCEPT_DOG);
    Dist dist_soul = bfs(board,SOUL);

    //2. 忍犬の数  -4000*num
    res-=dog_coef*int(board.dogs.size());

    //3.犬との距離 
    rep(y,1,H)rep(x,1,W){
        const int cxy=XY(x,y);
        int d=dist_ninja[cxy];
        if(d>=5) continue;
        res+=(30/(d+1))*min(40,dist_dog[cxy]);
    }

    //4. 犬に囲まれている スキルポイントを消費しないと打開できない -INF/2
    rep(y,1,H)rep(x,1,W){
        const int cxy=XY(x,y);
        if(dist_ninja[cxy]!=INF) res+=100;
    }

    int closed=0;
    rep(id,2){
        const int cxy=board.ninjas[id].xy;
        int dog_risk=0,move_risk=0,object_risk=0,safe=0;
        if(dist_dog[cxy]>=1000) safe++;

        rep(dir,4){
            const int nxy = cxy + dxy[dir];
            object_risk++;
            if(board.field[nxy].isWall()) continue;

            const int n2xy=nxy+dxy[dir];
            if(board.field[nxy].isObject() && board.field[n2xy].isObject()) continue;
            object_risk--;

            if(board.field[nxy].isObject() || board.field[n2xy].isObject() ) move_risk++;

            if(board.field[nxy].containsDog) dog_risk++;

        }

        //if(safe&&move_risk<=1 && move_risk+object_risk>=4) closed++;
        
        if(safe){
            if(move_risk<=1 && move_risk+object_risk>=4) closed++;
        }else{
            if(dog_risk >=1 && move_risk<=1 && dog_risk+move_risk+object_risk>=4 ) res-=INF/2;
        }
        
    }    

    if(closed==2) res-=INF/2;


    //1.忍者ソウルの取得数の係数を重めにする．20000 [0~2]
    res+=10000*(8-int(board.souls.size()));
    //2.スキルポイントもそこそこ 1000 [0~inf] 
    res+=skiilpoint_coef*board.skillPoint;
    //3.忍者ソウルとの距離 総和と最小値をコスト 総和[16~64] 最小値[ ~ ]　移動したことによる増加量のみを考慮
    rep(id,2){
        const int cxy = board.ninjas[id].xy;
        res+=3000*max(0,ninja_soul_prev[id]-dist_soul[cxy]);
    }

    return res;
}

inline bool my_simulation(State &board,int id0,int id1,int &res,int dog_num,bool stop=true){        
    const int idr[2]={id0,id1};
    res=0;

    rep(i,2){
        rep(j,board.number){
            const int opr=MOVE(idr[i],j);
            if(opr!=4 && (res+=100,simulateWalk(board,i,opr) == false) && stop ) return false;
        }
    }

    simulateDog(board,dog_num);
    simulateTurn(board);    
    if(board.dogs.empty()) res*=100;

    int tmp=score(board,ninja_soul_prev);
    res+=tmp;
    if(tmp <= -INF) res=-INF;
    return true;
}

inline int rival_simulation(State &board,int id0,int id1,int &res,bool stop=true){        
    const int idr[2]={id0,id1};
    res=0;

    rep(i,2){
        rep(j,board.number){
            const int opr=MOVE(idr[i],j);
            if(opr!=4 && (res+=100,simulateWalk(board,i,opr) == false) && stop ) return false;
        }
    }

    simulateTurn(board);
    if(board.dogs.empty()) res*=100;
    
    int tmp=score(board,dummy);
    res+=tmp;
    if(tmp <= -INF) res=-INF;
    return true;
}


void AI(int cur_depth,const Operation &op){
    const State board=get<0>(op);

    //cerr << "CALL AI: " << cur_depth << endl;
    
    // 最短距離が1のときには -INF
    {
        Dist dist_soul = bfs(board,SOUL);
        rep(id,2){
            int cxy = board.ninjas[id].xy;
            ninja_soul_prev[id]=dist_soul[cxy];
        }
    }


    int rival_nothing=-INF,rival_skill=-1,rival_point=-1,rival_id0=-1,rival_id1=-1,num_dog=0;
    
    {
        State cboard=rivalState[turn];
        rep(id0,cboard.upper)rep(id1,cboard.upper){
            State nboard=cboard;
            int res=0;
            if(rival_simulation(nboard,id0,id1,res)==false) continue;
            if(chmax(rival_nothing,res)){
                num_dog=8-int(nboard.souls.size());
                rival_id0=id0,rival_id1=id1;
            }
        }
    }

    {
        if(rival_nothing<=-INF/2){
            rep(y,1,H-1)rep(x,1,W-1){
                int skill=-1; 
                const Point p=XY(x,y);
                State cboard=rivalState[turn];

                //　スキル使用の判定
                if(cboard.field[p].isObject()) skill=3;
                if(cboard.field[p].isEmpty()) skill=5;
                if(simulateSkill(cboard,skill,p)){
                    rep(id0,cboard.upper)rep(id1,cboard.upper){
                        State nboard=cboard;
                        int res=0;
                        if(rival_simulation(nboard,id0,id1,res)==false) continue;
                        if(chmax(rival_nothing,res)){
                            num_dog=8-int(nboard.souls.size());
                            rival_skill=skill,rival_point=p;
                            rival_id0=id0,rival_id1=id1;
                        }
                    }
                }
            }
        }   
    }
    
    // cerr << "Rival skill: " << rival_skill << endl;
    // Only Move
    int best_score=-INF;

    {
        State cboard=board;
        simulateSkill(cboard,0,0);

        rep(id0,cboard.upper)rep(id1,cboard.upper){
            State nboard;
            int skill=-1;
            if(id0<21&&id1<21){
                nboard=board;
                skill=-1;
            }else{
                nboard=cboard;
                skill=0;
            }
            int res=0;
            if(my_simulation(nboard,id0,id1,res,num_dog)==false) continue;
            chmax(best_score,res);
            //cerr << res << endl;
            if(check[cur_depth].empty() || res > -INF) check[cur_depth].emplace_back(Operation(nboard,res,rival_nothing,id0,id1,skill,0));

        }

    }
   
    //cerr << get<1>(op) << " " << best_score << endl;
    
    // Rotation skill
    

    {
        const int skill=7;
        rep(i,2){
            State cboard=board;
            int add_dog=simulateSkill(cboard,skill,i);
            if(add_dog>=3 && cboard.skillPoint>=12){
                //cerr << "Rotation skill" << endl;
                rep(id0,cboard.upper)rep(id1,cboard.upper){
                    State nboard=cboard;
                    int res=0;
                    if(my_simulation(nboard,id0,id1,res,num_dog)==false) continue;
                    chmax(best_score,res);
                    if(check[cur_depth].empty() || res > -INF) check[cur_depth].emplace_back(Operation(nboard,res,rival_nothing-dog_coef*add_dog,id0,id1,skill,i)); 
                }
            }
        }
    }

    //cerr << get<1>(op) << " " << best_score << endl;

    {
        rep(y,1,H-1)rep(x,1,W-1){
            int skill=-1; 
            const Point p=XY(x,y);
            State cboard=board;

            //　スキル使用の判定
            if(cboard.field[p].isObject()) skill=3;
            if(cboard.field[p].isEmpty()) skill=5;
            if(simulateSkill(cboard,skill,p)){
                rep(id0,cboard.upper)rep(id1,cboard.upper){
                    State nboard=cboard;
                    int res=0;
                    if(my_simulation(nboard,id0,id1,res,num_dog)==false) continue;
                    chmax(best_score,res);
                    if(check[cur_depth].empty() || res > -INF) check[cur_depth].emplace_back(Operation(nboard,res,rival_nothing,id0,id1,skill,p));
                }
            }
        }
    }
    

    sort(_all(check[cur_depth]),
        [&](const Operation &a, const Operation &b){
            return get<1>(a)-get<2>(a) > get<1>(b)-get<2>(b);
        }
    );
    if(int(check[cur_depth].size())>threshold2) check[cur_depth].erase(begin(check[cur_depth])+threshold2,end(check[cur_depth])); 
    //cerr << get<1>(op) << " " << best_score << endl;
    
    if(cur_depth>=2) return;

    // Stone Attack from rivalAI
    
    if(rivalState[turn].skillPoint >= skills[2].cost && rival_skill == -1){
        //cerr << "Stone Attack from rivalAI" << endl;
        
        rep(i,int(check[cur_depth].size())){
            int id0,id1,skill,res;
            Point p;
            tie(ignore,res,ignore,id0,id1,skill,p)=check[cur_depth][i];

            int risk[2]={0,0},all[2]={0,0};
                
            rep(id,2){
                const int cxy=board.ninjas[id].xy;
                int risk_xy=-1,cmin=INF;

                rep(mx,-3,4)rep(my,-3,4){
                    int nx=X(cxy)+mx;
                    int ny=Y(cxy)+my;
                    if(nx<0||W<=nx) continue;
                    if(ny<0||H<=ny) continue;
                    
                    State nboard=board;
                    const int nxy=XY(nx,ny);

                    // 岩落とし
                    if(simulateSkill(nboard,1,nxy,false)==false) continue;
                        
                    //自スキル発動
                    simulateSkill(nboard,skill,p);
                    
                    int res=0;
                    my_simulation(nboard,id0,id1,res,num_dog,false);
                    
                    if(res <= -INF){
                        risk[id]++;
                        if(chmin(cmin,abs(mx)+abs(my))) risk_xy=nxy;
                    }
                    all[id]++;
                }
                
                
                //cerr << risk << " " << risk_xy << " " << Y(risk_xy) << " " << X(risk_xy) << endl;
                //cerr << risk << " " << skill << endl;
                if(risk[id] == 1 && skill == -1 && board.skillPoint >= skills[3].cost){
                    //cerr << "Thunder" << endl;
                    State nboard=board;
                    
                    //自スキル発動
                    simulateSkill(nboard,3,risk_xy);

                    int res=0;
                    my_simulation(nboard,id0,id1,res,num_dog,false);
                    
                    int id0,id1;
                    tie(ignore,ignore,ignore,id0,id1,ignore,ignore)=check[cur_depth][i];
                    check[cur_depth].emplace_back(Operation(nboard,res,rival_nothing,id0,id1,3,risk_xy));
                }
            }
            // risk 0ならば +INF/2
            if(risk[0]==0 && risk[1]==0) get<1>(check[cur_depth][i])+=INF/2;
            //risk 1は避けよう
            if(risk[0]==1 || risk[1]==1) chmin(get<1>(check[cur_depth][i]),-INF/2);

            if(risk[0]!=0 && risk[0]==all[0]) chmin(get<1>(check[cur_depth][i]),-INF/2);

            if(risk[1]!=0 && risk[1]==all[1]) chmin(get<1>(check[cur_depth][i]),-INF/2);
        }
    }

    // Avator Attack from rivalAI
    
    if(rivalState[turn].skillPoint >= skills[6].cost &&  rival_skill == -1){
        //cerr << "Avator Attack from rivalAI" << endl;
        
        rep(i,int(check[cur_depth].size())){
            int id0,id1,skill,res;
            Point p;
            tie(ignore,res,ignore,id0,id1,skill,p)=check[cur_depth][i];

            int risk[2]={0,0},all[2]={0,0},risk_xy[2]={-1,-1};

            rep(id,2){
                const int cxy=board.ninjas[id].xy;

                rep(mx,-3,4)rep(my,-3,4){
                    int nx=X(cxy)+mx;
                    int ny=Y(cxy)+my;
                    if(nx<0||W<=nx) continue;
                    if(ny<0||H<=ny) continue;
                    
                    State nboard=board;
                    const int nxy=XY(nx,ny);

                    // 影分身
                    if(simulateSkill(nboard,5,nxy,false)==false) continue;
                        
                    //自スキル発動
                    simulateSkill(nboard,skill,p);
                    
                    int res=0;
                    my_simulation(nboard,id0,id1,res,num_dog,false);
                    if(res <= -INF){
                        risk[id]++;
                        if(board.field[nxy].containsSoul) risk_xy[id]=nxy;
                    }
                    all[id]++;
                }
            }
            // risk 0ならば +INF/2
            if(risk[0]==0 && risk[1]==0) get<1>(check[cur_depth][i])+=INF/2;
            //risk 1は避けよう
            if(risk[0]==1 || risk[1]==1) chmin(get<1>(check[cur_depth][i]),-INF/2);

            if(risk[0]!=0 && risk[0]==all[0]) chmin(get<1>(check[cur_depth][i]),-INF/2);

            if(risk[1]!=0 && risk[1]==all[1]) chmin(get<1>(check[cur_depth][i]),-INF/2);

            if(rivalState[turn].skillCount[6]>0 && risk_xy[0]!=-1 && board.field[risk_xy[0]].containsSoul) chmin(get<1>(check[cur_depth][i]),-INF/2);

            if(rivalState[turn].skillCount[6]>0 && risk_xy[1]!=-1 && board.field[risk_xy[1]].containsSoul) chmin(get<1>(check[cur_depth][i]),-INF/2);
        }

    }
    
    int n=check[cur_depth].size();
    
    // Stone Attack from myAI
    if(rival_skill==-1){
        
        if(skills[2].cost <=4 && board.skillPoint >= skills[2].cost){ 
            int cmin_score=INF; 
            Point target=-1;

            rep(y,H)rep(x,W){
                const int xy=XY(x,y);
                int dist[2];
                rep(id,2){
                    int cxy=rivalState[turn].ninjas[id].xy;
                    dist[id]=abs(X(xy)-X(cxy))+abs(Y(xy)-Y(cxy));
                }
                if(dist[0]>=5 && dist[1]>=5) continue;
                State cboard=rivalState[turn];
                
                if(simulateSkill(cboard,1,xy,false)==false) continue;
                simulateSkill(cboard,rival_skill,rival_point); 
               
                State nboard=cboard;
                int res=0;
                if(rival_simulation(nboard,rival_id0,rival_id1,res)==false) continue;
                if(chmin(cmin_score,res)) target=xy;
            }
            
            if(cmin_score <= -INF){
                // cerr << "Stone Attack from myAI" << endl;
                //cerr << cmin_score << endl;
                //cerr << Y(target) << " " << X(target) << endl;
                rep(i,n){
                    State nboard;    
                    int id0,id1,skill,res;
                    Point p;
                    tie(nboard,res,ignore,id0,id1,skill,p)=check[cur_depth][i];
                    if(skill!=-1) continue;
                    skill=2,p=target;
                    if(simulateSkill(nboard,2,p)==false) continue;
                    res=score(nboard,ninja_soul_prev);
                    check[cur_depth].emplace_back(Operation(nboard,res,cmin_score,id0,id1,skill,p));
                }
            }

        }

    }else{

        // Avator Attack from myAI
        if(board.skillPoint >= skills[6].cost){ 
            int cmin_score=INF; 
            Point target=-1;

            rep(y,H)rep(x,W){
                const int xy=XY(x,y);
                State cboard=rivalState[turn];
                
                if(simulateSkill(cboard,5,xy,false)==false) continue;
                simulateSkill(cboard,rival_skill,rival_point); 
                
                State nboard=cboard;
                int res=0;
                if(rival_simulation(nboard,rival_id0,rival_id1,res)==false) continue;
                if(chmin(cmin_score,res)) target=xy;
            }
            
            if(cmin_score <= -INF){
                //cerr << "Avator Attack from myAI" << endl;
                //cerr << cmin_score << endl;
                //cerr << Y(target) << " " << X(target) << endl;
                rep(i,n){
                    State nboard;    
                    int id0,id1,skill,res;
                    Point p;
                    tie(nboard,res,ignore,id0,id1,skill,p)=check[cur_depth][i];
                    if(skill!=-1) continue;
                    skill=6,p=target;
                    if(simulateSkill(nboard,6,p)==false) continue;
                    res=score(nboard,ninja_soul_prev);
                    check[cur_depth].emplace_back(Operation(nboard,res,cmin_score,id0,id1,skill,p));
                }
            }

        }
    }
}


inline int fast_score(const State &board,const State &pboard,int base_score){
    int res=base_score;

    //1. 犬に追いつかれる -INF
    rep(id,2){
        const int cxy = board.ninjas[id].xy;
        if(board.field[cxy].containsDog) return -INF;
    }

    //2. 忍犬の数  -4000*num
    res-=dog_coef*(int(board.dogs.size())-int(pboard.dogs.size()));

    //4. 犬に囲まれている スキルポイントを消費しないと打開できない -INF/2

    rep(id,2){
        const int cxy=board.ninjas[id].xy;
        int dog_risk=0,move_risk=0,object_risk=0;
 
        rep(dir,4){
            const int nxy = cxy + dxy[dir];
            object_risk++;
            if(board.field[nxy].isWall()) continue;

            const int n2xy=nxy+dxy[dir];
            if(board.field[nxy].isObject() && board.field[n2xy].isObject()) continue;
            object_risk--;

            if(board.field[nxy].isObject() || board.field[n2xy].isObject() ) move_risk++;

            if(board.field[nxy].containsDog) dog_risk++;
        }
        if(dog_risk >=1 && move_risk<=1 && dog_risk+move_risk+object_risk>=4 ) res-=INF/2;
    }    

    //1.忍者ソウルの取得数の係数を重めにする．20000 [0~2]
    res+=10000*( (8-int(board.souls.size())) - (8-int(pboard.souls.size())) );
    //2.スキルポイントもそこそこ 1000 [0~inf] 
    res+=skiilpoint_coef*(board.skillPoint - pboard.skillPoint);
    //3.忍者ソウルとの距離 総和と最小値をコスト 総和[16~64] 最小値[ ~ ]　移動したことによる増加量のみを考慮
    rep(id,2){
        const int cxy = board.ninjas[id].xy;
        rep(dir,4){
            const int nxy = cxy + dxy[dir];
            if(board.field[nxy].isEmpty()==false) continue;
            if(board.field[nxy].containsSoul) res+=3000;
        }
    }
    return res;
}

inline bool fast_my_simulation(State &board,int id0,int id1,int &res){        
    const State pboard=board;
    const int idr[2]={id0,id1};

    rep(i,2){
        rep(j,board.number){
            const int opr=MOVE(idr[i],j);
            if(opr!=4 && simulateWalk(board,i,opr) == false) return false;
        }
    }

    simulateTurn(board);
    int tmp=fast_score(board,pboard,res);
    res=tmp;
    return true;
}

void fast_AI(int cur_depth,const Operation &op){
    const State board=get<0>(op);
    const int base_score=get<1>(op);
    Operation in=op;

    //cerr << "fast_AI" << endl;

    // Only Move
    int best_score=-INF;

    {
        State cboard=board;
        simulateSkill(cboard,0,0);
        rep(id0,cboard.upper)rep(id1,cboard.upper){
            State nboard;
            int skill=-1;
            if(id0<21&&id1<21){
                nboard=board;
                skill=-1;
            }else{
                nboard=cboard;
                skill=0;
            }
            int res=base_score;
            if(fast_my_simulation(nboard,id0,id1,res)==false) continue;
            chmax(best_score,res);
            if(check[cur_depth].empty() || res > -INF) get<0>(in)=nboard,get<1>(in)=res,check[cur_depth].emplace_back(in);
        }
    }

    return;
}

// Debug用のシミュレータ関数
int debug_simulate(const State &board,int id0,int id1,int skill,int p){
    State cboard=board;
    int res=0;
    simulateSkill(cboard,skill,p);
    my_simulation(cboard,id0,id1,res,false);

    // cerr << "NINJA" << endl;
    // rep(id,2) cerr << Y(cboard.ninjas[id].xy) << " " << X(cboard.ninjas[id].xy) << endl;
    // cerr << "DOG" << endl;
    // for(auto &dog:cboard.dogs) cerr << Y(dog.xy) << " " << X(dog.xy) << endl;
    return res;
}


inline void debug_output(const State &board){
    rep(y,H){
        rep(x,W) cerr << board.field[XY(x,y)].kind;
        cerr << endl;
    }
    cerr << "NINJA" << endl;
    rep(id,2) cerr << Y(board.ninjas[id].xy) << " " << X(board.ninjas[id].xy) << endl;
    cerr << "DOG" << endl;
    for(auto &dog:board.dogs) cerr << Y(dog.xy) << " " << X(dog.xy) << endl;

}

bool input() {
    //cerr << "INPUT" << endl;
    //cerr << "REMTIME_INPUT" << endl;
    cin >> remTime[turn];
    if(cin.eof()) return false;
    
    //cerr << "SKILLS_INPUT" << endl;
    int numOfSkills;
    cin >> numOfSkills;

    //cerr << "SKILLS_CLEAR" << endl;
    skills.clear();    

    //cerr << "SKILLS_INPUR" << endl;
    rep(i,numOfSkills) skills.emplace_back(Skill::input(i));
    myState[turn] = State::input(skills.size());
    rivalState[turn] = State::input(skills.size());
    
    if(rival_checkmate) rep(i,numOfSkills) critical_skill[i]+=rivalState[turn].skillCount[i]-rivalState[turn-1].skillCount[i];
    rival_checkmate=false;
    return true;
}

inline void output(int id0,int id1,int skill,Point p){
     if(0<=skill&&skill<8){
         cout << 3 << endl;
         if(skill==0)
             cout << skill << endl;
         else if(skill==7)
             cout << skill << " " << p << endl;
         else
             cout << skill << " " << Y(p) << " " << X(p) << endl;
     }else{
         cout << 2 << endl;
     }
 
     if(skill==0){   
         cout << ds[MOVE(id0,0)] << ds[MOVE(id0,1)] << ds[MOVE(id0,2)] << endl;
         cout << ds[MOVE(id1,0)] << ds[MOVE(id1,1)] << ds[MOVE(id1,2)] << endl;
     }else{
         cout << ds[MOVE(id0,0)] << ds[MOVE(id0,1)] << endl;
         cout << ds[MOVE(id1,0)] << ds[MOVE(id1,1)] << endl;
     }
     return;
 }


int main() {
    // AIの名前を出力
    string name=__FILE__;
    cout <<  name.substr(0,name.size()-4) << endl;
    cout.flush();
    
    while (input()){
        auto start = std::chrono::system_clock::now();      // 計測スタート時刻を保存
        // Beam Search
        check[0].emplace_back(Operation(myState[turn],score(myState[turn],dummy),0,0,0,0,0));

        int output_turn=1;

        rep(i,depth_limit){
            //cerr << "DEPTH " << i+1 << endl; 
            check[i+1].clear();
            for(auto &it:check[i]){
                if(i)
                    fast_AI(i+1,it);
                else
                    AI(i+1,it);
            }
            check[i].clear();
            //cerr << "States: " << check[i+1].size() << endl;
            sort(_all(check[i+1]),
                [&](const Operation &a, const Operation &b){
                    return get<1>(a)-get<2>(a) > get<1>(b)-get<2>(b);
                }
            );
            if(int(check[i+1].size())>threshold) check[i+1].erase(begin(check[i+1])+threshold,end(check[i+1])); 
            //cerr << "States: " << check[i+1].size() << " Score: " << get<1>(check[i+1][0]) << endl;

            output_turn=i+1;
            auto end = std::chrono::system_clock::now();
            auto dur = end - start;
            auto sec = std::chrono::duration_cast<std::chrono::seconds>(dur).count();
            if(sec >= 4.0) break;
        }
        
        // シャッフル
        {
            int m=1;
            const int sa=get<1>(check[output_turn][0])-get<2>(check[output_turn][0]);
            while(m<int(check[output_turn].size())){
                const int sb=get<1>(check[output_turn][m])-get<2>(check[output_turn][m]);
                if(sa!=sb) break;
                m++;
            }
            shuffle(begin(check[output_turn]), begin(check[output_turn])+m, mt);
        }

        // output
        
        State rboard;
        int id0,id1,skill,p;
        tie(rboard,myScore[turn],ignore,id0,id1,skill,p)=check[output_turn][0];
        output(id0,id1,skill,p);
        if(skill==2||skill==6) rival_checkmate=true;
        cout.flush();
        //#define CONSOLE
        #ifdef CONSOLE
            cerr << output_turn << endl;
            if(turn-1>=0) cerr << "Time: " << remTime[turn-1]-remTime[turn] << endl;
            cerr << myState[turn].skillPoint << endl;
            cerr << "Critical_skill ";
            rep(i,8) cerr << (i?" ":"") << critical_skill[i];
            cerr << endl;
            cerr << turn << endl;
            cerr << "Prediction score: " << myScore[turn] << endl;
            //rep(i,2,output_turn) debug_output(get<0>(check[i][0]));
            //cerr << "Final score: " << debug_simulate(myState[turn],id0,id1,skill,p) << endl;
            cerr << "Finished" << endl;
        #endif

        turn++;
    }
    return 0;
}