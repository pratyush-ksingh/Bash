#include <iostream>
#include <unistd.h>
#include <filesystem>
#include <vector>
#include <sys/wait.h>
#include <fcntl.h>
#include <signal.h>
#include <cstring>
#include <sys/syscall.h>
#include <limits.h>
#include <deque>
#include <stack>
#include <linux/input.h>
#include <termios.h>
#include <stdio.h>
#include <dirent.h>
#include <algorithm>
#include <sys/inotify.h>
#include <sys/types.h>
#include<fstream>
#include <ctime>
#include <map>
#include <sys/inotify.h>

using namespace std;

const int EVENT_SIZE = sizeof(struct inotify_event);
const int BUF_LEN = 1024 * (EVENT_SIZE + 16);
const int BUFFER_SZ = 256;
const int HIST_SZ = 10000;
const int HIST_DISP_SZ = 1000;
const char* hist_str = "history";
const int BUFF_SZ = 100;
const int TIMEOUT = 1;
bool watch = false;

static struct termios old, current;

size_t split(const std::string &txt, std::vector<std::string> &strs, char ch)
{
    size_t pos = txt.find( ch );
    size_t initialPos = 0;
    strs.clear();

    // Decompose statement
    while( pos != std::string::npos ) {
        strs.push_back( txt.substr( initialPos, pos - initialPos ) );
        initialPos = pos + 1;

        pos = txt.find( ch, initialPos );
    }

    // Add the last one
    strs.push_back( txt.substr( initialPos, std::min( pos, txt.size() ) - initialPos + 1 ) );

    return strs.size();
}

void removeTrailingCharacters(std::string &str, const char charToRemove) {
    str.erase (str.find_last_not_of(charToRemove) + 1, std::string::npos );
}

void removeLeadingCharacters(std::string &str, const char charToRemove) {
    str.erase(0, std::min(str.find_first_not_of(charToRemove), str.size() - 1));
}

/* Initialize new terminal i/o settings */
void initTermios(int echo) 
{
    tcgetattr(0, &old); /* grab old terminal i/o settings */
    current = old; /* make new settings same as old settings */
    current.c_lflag &= ~ICANON; /* disable buffered i/o */
    if (echo) {
        current.c_lflag |= ECHO; /* set echo mode */
    } else {
        current.c_lflag &= ~ECHO; /* set no echo mode */
    }
    tcsetattr(0, TCSANOW, &current); /* use these new terminal i/o settings now */
}

/* Restore old terminal i/o settings */
void resetTermios(void) 
{
    tcsetattr(0, TCSANOW, &old);
}

/* Read 1 character - echo defines echo mode */
char getch_(int echo) 
{
    char ch;
    initTermios(echo);
    ch = getchar();
    resetTermios();
    return ch;
}

/* Read 1 character without echo */
char getch(void) 
{
    return getch_(0);
}

/* Read 1 character with echo */
char getche(void) 
{
    return getch_(1);
}

bool IsProcessAlive(int ProcessId)
{
    // Wait for child process, this should clean up defunct processes
    waitpid(ProcessId, nullptr, WNOHANG);
    // kill failed let's see why..
    if (kill(ProcessId, 0) == -1)
    {
        // First of all kill may fail with EPERM if we run as a 
        // different user and we have no access, so let's make 
        // sure the errno is ESRCH (Process not found!)

        if (errno != ESRCH)
        {
            return true;
        }
        return false;
    }
    // If kill didn't fail the process is still running
    return true;
}

string cmd; // Stores the command
char cwd[BUFFER_SZ]; // Current Working Dir
vector<string> cmds; // 2D array of strings -> contains cmds seperated by pipe -> each cmd is seperated by space
char **argv; // array of args to be sent to execvp
int sz; // size of argv
bool is_bg = false;
pid_t fg = -1; // current foreground process
deque<string> q; // keeps the history of processes
vector<pid_t> p_list;   // utility for multiwatch
bool _watch = false;    // utility for multiwatch
pid_t _watch_p = -1; // utility for multiwatch
int LCS(string& s, string& t) {
    int n = s.length(), m = t.length();
    vector<vector<int>> dp(n + 1, vector<int>(m + 1, 0));
    int res = 0;
    for(int i = 1; i <= n; ++i) {
        for(int j = 1; j <= m; ++j) {
            dp[i][j] = (s[i - 1] == t[j - 1]) ? dp[i - 1][j - 1] + 1: max(dp[i - 1][j], dp[i][j - 1]);
            res = max(res, dp[i][j]);
        }
    }
    return res;
}

int match_cmd(string& t, string& best_match) {
    best_match = "No match for search term in history";
    int matched_len = 0;
    stack<string> tmp;
    while(q.size()) {
        string cur = q.back();
        tmp.push(cur);
        q.pop_back();
        if(t == cur) {
            best_match = cur; matched_len = t.length(); break;
        }
        else {
            // perform LCD DP here
            int len = LCS(cur, t);
            if(len > matched_len and len > 2) {
                matched_len = len;
                best_match = cur;
            }
        }
    }

    while(!tmp.empty()) {
        q.push_back(tmp.top());
        tmp.pop();
    }
    if(matched_len == 0)
        return -1;
    else
        return 0;
}

void prompt() {
    // Resets the error flags and the EOF indicator for the given file stream.
    clearerr(stdin); 
    getcwd(cwd, BUFFER_SZ);
    cout << string(cwd) << " >> ";
    int prompt_len = strlen(cwd) + 4;
    unsigned char c;
    cmd.clear();
    int ip_cnt = 0; // No of characters user i/p-ed so far
    fflush(stdout);
    while((c = getch()) != EOF) {
        // Arrow keys
        if(c == '\033') {
            getch(); // Read the [
            c = getch();
            // Ignore arrow keys. Maybe implement later?? ::Nope
            switch(c) {
                case 'A':
                    // code for arrow up
                    break;
                case 'B':
                    // code for arrow down
                    break;
                case 'C':
                    // code for arrow right
                    break;
                case 'D':
                    // code for arrow left
                    break;
            }

        }
        else if(c == '\t') { // Auto-complete
            vector<string> match; // Contains list of best matches
            int best_len = 0;
            string pref = ""; // Stores the prefix of the filename to be searched
            int i = ip_cnt - 1;
            while(i >= 0 and cmd[i] != ' ' and cmd[i] != '>' and cmd[i] != '<')
                pref += cmd[i--];
            reverse(pref.begin(), pref.end());

            DIR *dpdf;
            struct dirent *epdf;
            dpdf = opendir("./");

            if (dpdf != NULL){
               while (epdf = readdir(dpdf)){
                    if(epdf -> d_type == DT_REG){
                        string file_name = string(epdf -> d_name);
                        int i = 0;
                        int n = min(file_name.length(), pref.length());
                        while(i < n and file_name[i] == pref[i]) i++;
                        if(i) {
                            if(i == best_len)
                                match.push_back(file_name);
                            else if(i > best_len) {
                                match.clear();
                                match.push_back(file_name);
                                best_len = i;
                            }
                        }
                    }
               }
            }
            closedir(dpdf);
            if(match.size() == 1) {
                // print the remaining chars
                for(int i = pref.length(); i < match[0].length(); ++i) {
                    cout << match[0][i]; cmd += match[0][i]; ip_cnt++;
                }
            }
            else if(match.size() > 1){
                cout << endl;
                int cnt = 0;
                for(string& s: match) {
                    cout << (++cnt) << ". " << s << ' ';
                }
                int x;
                bool stop = false;
                while(true) {
                    cout << "\nEnter the desired file no: ";
                    x = 0;
                    clearerr(stdin);
                    char* line = NULL; size_t len;
                    int sz = getline(&line, &len, stdin);
                    if(sz > 0) {
                        for(int i = 0; i < sz - 1; ++i){
                            if(line[i] >= '0' and line[i] <= '9')
                                x = x * 10 + (line[i] - '0');
                            else {
                                x = 0; break;
                            }
                        }
                    }
                    else {
                        stop = true;
                        cout << string(cwd) << " >> " << cmd;
                        break;
                    }
                    free(line);
                    if(x <= 0 or x > match.size())
                        cout << "Invalid file no!";
                    else
                        break;
                }
                if(!stop) {
                    for(int i = pref.length(); i < match[x - 1].length(); ++i) {
                        cmd += match[x - 1][i]; ip_cnt++;
                    }
                    cout << string(cwd) << " >> " << cmd;
                    fflush(stdin);
                }
            }
        }
        else if((int)c == 18) { // Search prompt
            int tot = prompt_len + ip_cnt; // Total amount of chars currently on the terminal
            for(int i = 0; i < tot; ++i) {
                cout << '\b' << ' ' << '\b'; 
            }
            cout << "Enter search term: ";
            clearerr(stdin);
            char* line = NULL; size_t len;
            int sz = getline(&line, &len, stdin);
            string search_cmd;
            if(sz <= 1) {
                cout << string(cwd) << " >> ";
                ip_cnt = 0;
                continue;
            }
            search_cmd = string(line);
            string res;
            if(match_cmd(search_cmd, res) == -1){
                cout << res << endl;
                cout << string(cwd) << " >> ";
                cmd.clear(); ip_cnt = 0; fflush(stdout);
            }
            else {
                cout << string(cwd) << " >> ";
                cmd = res; ip_cnt = res.length(); fflush(stdout);
                cout << res;
            }
        }
        else if((int)c == 127) {  // backspace
            if(ip_cnt == 0) continue; // Don't remove anymore chars
            cout << '\b' << ' ' << '\b';
            cmd.pop_back();
            ip_cnt--;
        }
        else if((int)c == 255) {    // Ctrl-C interrupt
            cout << string(cwd) << " >> ";
            cmd.clear(); ip_cnt = 0;
            fflush(stdout);
        }
        else{
            ip_cnt++;
            cout << c;
            if(c == '\n') break;
            cmd += c;
        }
    }

    if(cmd.size()) {
        if(q.empty() or q.back() != cmd) { // Only push if last command was not the same or empty
            if(q.size() == HIST_SZ)
                q.pop_front();
            q.push_back(cmd);
        }
    }
}

void clear_cmds() {
    for(int i = 0; i < cmds.size(); ++i)
        cmds[i].clear();
    cmds.clear();
}

void process_cmd(string command) {
    clear_cmds();
    is_bg = false;
    while(command.length() and (command.back() == ' ' or command.back() == '\t')) command.pop_back();
    if(command.length() and command.back() == '&'){
        is_bg = true;
        command.pop_back();
    }

    command.push_back('|');
    int n = command.length();
    for(int j = 0, i = 0; j < n; ++j) {
        if(command[j] == '|') {
            cmds.push_back(command.substr(i, j - i));
            i = j + 1;
        }
    }
    command.pop_back();
}

// Prints the pipe seperated commands
void debug_cmd() {
    cout << "No of pipe seperated commands: " << cmds.size() << endl;
    for(string& s: cmds)
        cout << s << endl;
}

void getfile(string& command, int& fd, char c) {
    int n = command.length();
    bool last = true; // last file = fd
    for(int i = n - 1; i >= 0; --i) {
        if(command[i] == c) {
            // get the filename
            char *str = NULL; int j = i + 1;
            while(j < n) {
                if(command[j] == ' ') j++;
                else {
                    // file name starts here
                    int k = j;
                    while(k < n and command[k] != ' ' and command[k] != '<' and command[k] != '>') k++;
                    str = (char *)malloc((k - j + 1) * sizeof(char));
                    str[k - j] = '\0';
                    for(int p = j; p < k; ++p)
                        str[p - j] = command[p];

                    if(c == '<') { // i/p file
                        int file_fd = open(str, O_RDONLY, S_IRUSR | S_IWUSR);
                        if(file_fd < 0) {
                            if(fd >= 0) close(fd);
                            fd = -1; return;
                        }
                        if(last) 
                            fd = file_fd, last = false;
                        else
                            close(file_fd);
                    }
                    else { // o/p file
                        int file_fd = open(str, O_WRONLY | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR);
                        if(file_fd < 0) {
                            if(fd >= 0) close(fd);
                            fd = -1; return;
                        }
                        if(last) 
                            fd = file_fd, last = false;
                        else
                            close(file_fd);
                    }
 
                    break;
                }
            }
            n = i;
        }
    }
}

void build_argv(int& in, int& out, int i) {
    // free the resources
    for(int i = 0; i < sz; ++i)
        free(argv[i]);
    free(argv);
    
    string command = cmds[i];
    int n = command.length();
    sz = 0;
    for(int i = 0; i < n; ++i) {
        if(command[i] == ' ' or command[i] == '\t') continue;
        else if(command[i] == '<' or command[i] == '>') break;
        else {
            sz++;
            while(i < n and command[i] != '<' and command[i] != ' ' and command[i] != '>' and command[i] != '\t') i++;
        }
    }

    argv = (char **)malloc((sz + 1) * sizeof(char *));
    argv[sz] = NULL;
    for(int i = 0, st = 0; i < n; ) {
        if(command[i] == ' ' or command[i] == '\t') {i++; continue;}
        else if(command[i] == '<' or command[i] == '>') break;
        else {
            int j = i;
            while(i < n and command[i] != '<' and command[i] != ' ' and command[i] != '>' and command[i] != '\t') i++;
            argv[st] = (char *)malloc((i - j + 1) * sizeof(char));
            int k = 0;
            while(j < i)
                argv[st][k++] = command[j++];
            argv[st][k] = '\0';
            st++;
        }
    }

    // Rules <- check???
    //1. order between i/p and o/p files doesn't matter (only within matters)
    //2. i/p is taken only from the last i/p file
    //3. o/p is written only in the last o/p file. All other o/p files are created (if not exist) and **made blank**
    //4. If any of the file produces error on open() => error
    getfile(command, in, '<');
    getfile(command, out, '>');
}

void sig_handler(int sig){
    watch = false;
    char str[] = "\n";
    write(0, str, strlen(str));
    fg = -1;
    if(sig == SIGINT and fg != -1) {
        kill(fg, SIGKILL); // kllls the process
    }
    else if(sig == SIGTSTP and fg != -1) {
        kill(fg, SIGCONT); // send a signal to continue the foreground process
    }
    fg = -1;
}

int execute_hist() {
    stack<string> tmp;
    int cnt = HIST_DISP_SZ;
    int pos = 1;
    while(q.size() and cnt) {
        tmp.push(q.back());
        q.pop_back();
    }

    while(!tmp.empty()) {
        cout << pos << ". " << tmp.top() << '\n';
        q.push_back(tmp.top());
        tmp.pop();
        pos++;
    }
    return 0;
}

// Reads history on start-up
void read_history() {
    FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;

    fp = fopen("./history.txt", "r");
    if (fp == NULL) {
        fopen("./history.txt", "w"); 
        fclose(fp);
        return;
    }

    while ((read = getline(&line, &len, fp)) != -1) {
        line[read - 1] = '\0';
        q.push_back(string(line));
    }

    fclose(fp);
    if (line)
        free(line);
}

// Writes back history during shutdown
void write_history() {
    FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;

    fp = fopen("./history.txt", "w");
    if (fp == NULL) {
        cout << "Couldn't open history.txt file!\n";
        return;
    }

    while(q.size()) {
        string tmp = q.front(); tmp.push_back('\n');
        fputs(tmp.c_str(), fp);
        q.pop_front();
    }

    fclose(fp);
    if (line)
        free(line);
}

int create_process(int in, int out, int i) {
    pid_t pid = fork();
    int status;
    if(0 == pid) {
        // child process

        // Builds the argv and modifies in and out in case of redirections
        // < or > has more precendence over pipe <- check????? <- e.g ls -l | cat < hello.txt
        build_argv(in, out, i);

        // Invalid redirection
        if(in == -1 or out == -1)
            exit(EXIT_FAILURE);
        if(in != 0){
            dup2(in, 0);
            close(in);
        }

        if(out != 1) {
            dup2(out, 1);
            close(out);
        }
        if(strcmp(argv[0], hist_str) == 0) {
            if(execute_hist() == -1)
                exit(EXIT_FAILURE);
            exit(EXIT_SUCCESS);
        } 

        execvp(argv[0], argv);
        exit(errno);
    }
    else if(pid < 0) {
        cout << "Can't create child process" << endl;
        return -1;
    }
    else {
        if(!is_bg) {
            fg = pid; // set the current fg process
        }
        waitpid(pid, &status, 0);
        if(WIFEXITED(status)){
            if(WEXITSTATUS(status)){
                printf("Error: process exited with status code: %d\n", WEXITSTATUS(status));
                return -1; // Stop execution of piped commands
            }
        }
        return 0;
    }
}

int process_handler(struct sigaction sa, int _stdout = 1){
    if(is_bg) {
        pid_t pid = fork();
        if(0 == pid) {
            sa.sa_handler = SIG_DFL;
            if(sigaction(SIGINT, &sa, NULL) == -1)
                cout << "Couldn't catch SIGINT - Interrupt Signal\n";
            if(sigaction(SIGTSTP, &sa, NULL) == -1)
                printf("Couldn't catch SIGTSTP - Suspension Signal\n");

            // SIGINT signal is sent to all processes of the foreground process group (fgid)
            // To not terminate bg process we give the bg processes a different process grp (= child pid)
            // than our shell (whose PID will be the fgid)
            if (setpgid(0, 0) < 0) {
                perror("setpgid");
                exit(EXIT_FAILURE);
            }
            int fd[2]; // pipe
            int in = 0; // input fd of the command
            int sz = cmds.size();
            for(int i = 0; i < sz; ++i) {
                int ret;
                if(i == sz - 1) {
                    // last command should write to stdout
                    ret = create_process(in, _stdout, i);
                }
                else {
                    pipe(fd);
                    ret = create_process(in, fd[1], i);
                    close(fd[1]); // No need of fd[1] anymore
                    in = fd[0]; // Next child will read from fd[0]
                }
                if(ret == -1) exit(EXIT_FAILURE);
            }
            exit(EXIT_SUCCESS);
        }
        else if(pid < 0) {
            cout << "Can't create child process" << endl;
        }
    }
    else {
        int fd[2]; // pipe
        int in = 0; // input fd of the command
        int sz = cmds.size();
        for(int i = 0; i < sz; ++i) {
            int ret;
            if(i == sz - 1) {
                // last command should write to stdout
                ret = create_process(in, _stdout, i);
            }
            else {
                pipe(fd);
                ret = create_process(in, fd[1], i);
                close(fd[1]); // No need of fd[1] anymore
                in = fd[0]; // Next child will read from fd[0]
            }
            if(ret == -1) return -1;
        }
    }   
    return 0;
}

int main() {
    read_history(); // Read history from local file
    struct sigaction sa;

    sa.sa_handler = sig_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;

    // If conditions for signal handling.Also creates 2 signal handlers in memory for the SIGINT and SIGTSTP
    if(sigaction(SIGINT, &sa, NULL) == -1)
        cout << "Couldn't catch SIGINT - Interrupt Signal\n";
    if(sigaction(SIGTSTP, &sa, NULL) == -1)
        printf("Couldn't catch SIGTSTP - Suspension Signal\n");
	while(true) {
        int status;
        // Check for zombie process
        while(true) {
            status = waitpid(-1, &status, WNOHANG);
            if(status <= 0) break;
        }
        
        prompt();
        process_cmd(cmd);
        if(cmd == "quit") { write_history(); exit(EXIT_SUCCESS);}
        
        vector<string> v,commands; int cnt=0;
        split( cmd, v, ' ' );

        if(v[0] == "multiWatch"){
            watch = true;
            _watch_p = getpid();
            int n = cmd.length();
            bool flag=false;
            string temp = cmd.substr(10+1),temp1;
            removeTrailingCharacters(temp,' ');
            removeLeadingCharacters(temp,' ');
            for(int i = 0;i < temp.length(); i++){
                if(temp[i] == '"')flag=true;
                else if(!(temp[i]==' ' or temp[i]==',' ))flag=false;
                if(flag){
                    if(temp[i] != ' ') temp1.push_back(temp[i]);
                }
                else{
                    temp1.push_back(temp[i]);
                }
            }
            split(temp1,commands,',');
            for(string&i:commands){
                removeTrailingCharacters(i,'"');
                removeLeadingCharacters(i,'"');
            }
            cnt = commands.size();
            vector<pair<string, string>> cmd_file_pair;
            map<string, pid_t> file_fds;

            for(int i = 0; i < cnt; i++){
                process_cmd(string(commands[i]));
                pid_t child_pid = fork();
                if (child_pid < 0) {
                    perror("fork");
                    abort();
                } 
                else if(child_pid == 0) {
                    // DoWorkInChild();
                    string filename = ".temp."+to_string(getpid()) + ".txt";
                    int file_fd = open(filename.c_str(), O_WRONLY | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR); // Open a file for writing
                    int ret = process_handler(sa, file_fd);
                    close(file_fd);
                    if(ret == 0) exit(EXIT_SUCCESS);
                    else
                        exit(EXIT_FAILURE);
                }
                else {
                    // Parent
                    string filename = ".temp."+to_string(child_pid) + ".txt";
                    int file_fd = open(filename.c_str(), O_RDWR | O_CREAT, S_IRUSR | S_IWUSR); // Open a file for reading..create if non-existing
                    if(file_fd == -1) {
                        cout << "File can't be opened for reading|...\n";
                        exit(EXIT_FAILURE);
                    }
                    // close(file_fd);
                    cmd_file_pair.push_back({string(commands[i]), filename});
                    file_fds[filename] = file_fd;
                }
            }
            
            int fd = inotify_init();

            if(fd < 0) {
                perror("inotify_init");
            }
            else {
                map<int, pair<string, string>> mp;    // wd, command name pair
                
                for(auto s: cmd_file_pair) {
                    string path = s.second;
                    int wd = inotify_add_watch(fd, path.c_str(), IN_MODIFY | IN_CLOSE_WRITE);
                    if(wd < 0) {
                        cout << "Error in inotify\n";
                    }
                    mp[wd] = {s.first, s.second};
                }

                // Now use select  
                fd_set readset, master;
                FD_ZERO(&readset);
                FD_ZERO(&master);
                FD_SET(fd, &master);
                FD_SET(fd, &readset);
                char buff[BUFF_SZ];
                char inotify_BUFF[BUF_LEN];
                struct timeval timeout = {TIMEOUT, 0}; // 10 sec. timeout
                int files_closed = 0;   // Keeps track of how many files opened for write are closed
                while(watch) {
                    readset = master;
                    int status;
                    if(files_closed == cmd_file_pair.size())
                        status = select(fd + 1, &readset, NULL, NULL, &timeout);
                    else
                        status = select(fd + 1, &readset, NULL, NULL, NULL);
                    if (status == -1) {
                        break;
                    }
                    
                    // Time out
                    if(status == 0) {
                        break;
                    }

                    if(FD_ISSET(fd, &readset)) {
                        int length = read(fd, inotify_BUFF, BUF_LEN);  
                        if (length < 0 ) {
                            perror( "read" );
                        }  
                        int i = 0;
                        while (i < length) {
                            struct inotify_event *event = (struct inotify_event *)&inotify_BUFF[i];
                            uint32_t mask = event -> mask;
                            if (mask & IN_MODIFY) {
                                int read_fd = file_fds[mp[event -> wd].second];
                                bool first = true;
                                while(watch) {
                                    int sz = read(read_fd, buff, BUFF_SZ - 1);
                                    if(sz <= 0) {
                                        if(!first)
                                            cout<<"\n->->->->->->->->->->->->->->->->->->->\n";
                                        break;
                                    }
                                    buff[sz] = '\0';
                                    if(first) {
                                        time_t result = std::time(nullptr);
                                        cout << "\n\"" << mp[event -> wd].first << "\", ";
                                        string t = std::asctime(std::localtime(&result)); t.pop_back();
                                        cout << t << " :\n";
                                        cout << "<-<-<-<-<-<-<-<-<-<-<-<-<-<-<-<-<-<-<-" << endl;
                                        first = false;
                                    }
                                    printf("%s", buff);
                                }
                            }
                            if(mask & IN_CLOSE_WRITE) { // Check if the file opened for write is closed
                                files_closed++;
                            }
                            i += EVENT_SIZE + event -> len;
                        }
                    }
                }

                // Close the file fds
                for(auto itr: file_fds) 
                    close(itr.second);
                
                // Delete all the files
                DIR *dr;
                struct dirent *en;
                dr = opendir("./"); //open all directory
                if (dr) {
                    while ((en = readdir(dr)) != NULL) {
                        string name = en->d_name;
                        if (name.rfind(".temp.", 0) == 0) {
                            int i = remove(name.c_str());
                        }
                    }
                    closedir(dr); 
                }

                // Close the inotify event
                int ret;
                for(auto itr: mp) {
                    inotify_rm_watch (fd, itr.first);
                    if (ret)
                        perror ("inotify_rm_watch");
                }

                ret = close (fd);
                if (ret)
                    perror ("close");
            }
        }
        else {
            process_handler(sa);
        }
    }
}