read -p "Name of project? [Recommended: use lowercase, and if it is many words, use kebab-case] : " new_proj_name

# author name
read -p "GitHub username? [Default: dannypsnl] : " username
if [ -z $username ]; then
    echo "keep origin github id"
else
    sed -i "" "s/dannypsnl/$username/g" ./info.rkt
    sed -i "" "s/dannypsnl/$username/g" ./README.md
fi
read -p "your only name? [Default: Lîm Tsú-thuàn] : " yourname
if [ -z $yourname ]; then
    echo "keep origin author name"
else
    sed -i "" "s/Lîm Tsú-thuàn/$yourname/g" ./scribblings/racket-project.scrbl
    sed -i "" "s/Lîm Tsú-thuàn/$yourname/g" ./LICENSE-MIT
fi

# repo name
sed -i "" "s/racket-project/$new_proj_name/g" ./info.rkt
sed -i "" "s/racket-project/$new_proj_name/g" ./main.rkt
sed -i "" "s/racket-project/$new_proj_name/g" ./scribblings/racket-project.scrbl
sed -i "" "s/racket-project/$new_proj_name/g" ./README.md

mv ./scribblings/racket-project.scrbl ./scribblings/$new_proj_name.scrbl
